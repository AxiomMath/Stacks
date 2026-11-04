module

public import Mathlib.CategoryTheory.Limits.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Absolute Noetherian approximation for algebraic spaces

A quasi-compact and quasi-separated algebraic space over `Spec ℤ` is the limit of a
directed inverse system of algebraic spaces which are quasi-separated and of finite type
over `Spec ℤ`, with affine transition morphisms. This file records the *conclusion* of that
statement as a reusable interface, together with the closure properties of affineness and
the descent step which its proof ends with.

The proposition itself is **not** proved here, and nothing in this file carries the tag
`07SU`. Its proof in the source runs through a finite stratification of the space by open
subspaces with étale scheme neighbourhoods, absolute Noetherian approximation for *schemes*,
an approximation of étale morphisms, a gluing construction of étale equivalence relations
stagewise, and finally the identification of the two quotients. The source cites seventeen
tags, of which fifteen are statements; of those fifteen this development has five. See the
implementation notes for the audit.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianApproximation` is the conclusion of the proposition as
  data: a directed set, an inverse system of algebraic spaces over it with affine transition
  morphisms, each stage quasi-separated and of finite type over `Spec ℤ`, and a limiting
  cone with the given space as its vertex.
* `AlgebraicGeometry.Space.HasNoetherianApproximation` is the corresponding proposition,
  `Nonempty` of the above. This is the hypothesis a client of the unproved proposition
  should carry.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_id`: affineness of a morphism of presheaves on the
  big fppf site contains the identities. Together with the stability under composition in
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Affine.lean` and the base-change
  stability in `StacksFrontier/AlgebraicGeometry/Descent/AffineHomFpqcLocal.lean` this is what
  an inverse system with affine transition morphisms is built and consumed with.
* `AlgebraicGeometry.Space.NoetherianApproximation.ofIso` transports an approximation along
  an isomorphism, and `AlgebraicGeometry.Space.NoetherianApproximation.const` is the base
  case: a space which is already quasi-separated and of finite type over `Spec ℤ` is its own
  approximation, over a one-element directed set.
* `AlgebraicGeometry.Space.exists_iso_of_common_presentation`: two algebraic spaces with the
  same surjective étale atlas and the same kernel pair on it are isomorphic, compatibly with
  the atlases, and `AlgebraicGeometry.Space.exists_iso_of_isomorphic_presentations` is the
  same with the two kernel pairs merely isomorphic as relations. This is the final step of
  the proof of the proposition, where the constructed limit `X' = lim X_i` is identified
  with `X`.

## Implementation notes

*The index category.* The source asks for a directed set `I` and an inverse system over it,
so the index is a nonempty directed preorder and the system is a functor out of `Iᵒᵖ`. This
is deliberately *not* relaxed to `CategoryTheory.IsCofiltered`, which is the shape the
limit machinery of this development is stated for (`AlgebraicGeometry.Space` closed
immersions of limits, and Stacks 07SF): relaxing it would weaken the conclusion. The two are
bridged by instance synthesis — for a nonempty directed preorder `I` the category `Iᵒᵖ` is
cofiltered — so after `letI := A.preorder; letI := A.nonempty; letI := A.isDirected` a
client has `CategoryTheory.IsCofiltered (A.I)ᵒᵖ` and may feed `A.diagram` to that machinery.

*The limit.* `X = lim X_i` is recorded as a limiting cone of *presheaves* with vertex `X`.
This is equivalent to the source's limit in the category of algebraic spaces: that category
is a full subcategory of presheaves containing the representables, so the universal property
against algebraic spaces determines the sections of the limit on every object of the site.
Limits of this shape exist unconditionally, so no size hypothesis is needed to state the
conclusion; the cardinality bounds that Stacks 07SF carries are needed to *construct* such a
limit and recognize it as an algebraic space, not to say that a given space is one.

*Finite type over `Spec ℤ`.* The terminal scheme represents `Spec ℤ`. A stage is viewed over
it with `AlgebraicGeometry.Space.viewOverIntegers` (Stacks 03I5 (2)), and its structure
morphism is the morphism to the terminal presheaf on the big fppf site of the terminal
scheme; finite type is `AlgebraicGeometry.Space.IsFiniteType` of that morphism, which is
locally of finite type on every étale chart together with quasi-compactness. The source's
other phrasing of the same system, "of finite presentation over `Spec ℤ`", is equivalent by
Stacks 06G4 over the Noetherian base `Spec ℤ`; 06G4 is not available here, so the predicate
uses the wording of the proposition itself.

*What the proof needs.* The seventeen tags cited by the source are 07ST, 05W5, 01ZA, 07SK,
07SL, 07SR, 07RN, 01JA, 02WW, 07S4, 040W, 040Y, 07SV, 07S3, 03WG, 07SF and 0262. Two of them
are not statements, and so are not inputs to be formalized: 01JA is the *section* on glueing
schemes along a common open, a construction carried out here by
`AlgebraicGeometry.Scheme.gluePair` in
`StacksFrontier/AlgebraicGeometry/NoetherianApproximation/GluePair.lean`, and 07SV is the
label of a displayed cartesian square inside the proof of 07SU itself.

Of the fifteen cited statements, five are formalized in this development:

* 0262, in `StacksFrontier/AlgebraicGeometry/Spaces/Presentation/KernelPair.lean`;
  `exists_iso_of_common_presentation` below is the use the proof makes of it.
* 02WW, the quotient of an étale equivalence relation, by which every stage `X_i` of the
  system is constructed, in
  `StacksFrontier/AlgebraicGeometry/Spaces/QuotientSheafPresentationUnconditional.lean`.
* 03WG, in `StacksFrontier/AlgebraicGeometry/Descent/AffineHomEtaleDescent.lean`; this is what
  makes the transition morphisms `X_i → X_{i'}` affine.
* 07S4, in `StacksFrontier/AlgebraicGeometry/Spaces/QuasiSeparatedAbsolute.lean`.
* 07SF, in `StacksFrontier/AlgebraicGeometry/Spaces/AffineLimitExistence.lean`, by which the
  limit `X' = lim X_i` is formed.

The ten that are missing are 07ST, 05W5, 01ZA, 07SK, 07SL, 07SR, 07RN, 040W, 040Y and 07S3.
Three of them — 040W, 040Y and 07S3 — have all of their own cited inputs formalized here; the
other seven do not. Two of those seven carry the mathematical weight of the proposition. The
first is 07ST, the stratification of a quasi-compact quasi-separated algebraic space by open
subspaces admitting surjective étale morphisms from quasi-compact separated schemes which are
isomorphisms over the strata; nothing of its shape exists here. The second is absolute
Noetherian approximation for *schemes*, Stacks 01ZA, which has no formalization in this
development and none in Mathlib, which has the inverse-limit theory of schemes with affine
transition morphisms but not the approximation theorem that produces such a system. The one
lemma 01ZA rests on, 07RN, is reduced in
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeApproximation/Induction.lean` to the
single-affine-open step `IsOneAffineOpenStep`, which that file still carries as a hypothesis
rather than proving.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Closure properties of affineness -/

/-- The identity morphism of a presheaf on the big fppf site of `S` is affine. -/
theorem isAffineHom_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsAffineHom B S hS (𝟙 F) := by
  intro Z k
  exact ⟨Z, k, 𝟙 _, by
    simpa using IsPullback.of_vert_isIso (fst := k) (snd := (𝟙 _ : _ ⟶ _)) ⟨by simp⟩⟩

/-! ### The conclusion of absolute Noetherian approximation -/

/-- A *Noetherian approximation* of a presheaf `X` on the big fppf site of `S`: a nonempty
directed set `I`, an inverse system of algebraic spaces indexed by `I` whose transition
morphisms are affine and whose stages are quasi-separated and of finite type over
`Spec ℤ`, and an identification of `X` with the limit of that system.

This is the conclusion of Stacks 07SU, absolute Noetherian approximation, which asserts that
every quasi-compact and quasi-separated algebraic space over `Spec ℤ` admits one. That
assertion is not proved in this development; a client should carry
`AlgebraicGeometry.Space.HasNoetherianApproximation` as a hypothesis. -/
structure NoetherianApproximation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The directed set indexing the system. -/
  I : Type u
  /-- Its order. -/
  [preorder : Preorder I]
  /-- A directed set is nonempty. -/
  [nonempty : Nonempty I]
  /-- A directed set is directed. -/
  [isDirected : IsDirected I (· ≤ ·)]
  /-- The inverse system, a functor out of the opposite of the index set. -/
  diagram : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Every stage is an algebraic space over `S`. -/
  isAlgebraicSpace (j : Iᵒᵖ) : IsAlgebraicSpace B S hS (diagram.obj j)
  /-- The transition morphisms are affine. -/
  isAffineHom_map {j j' : Iᵒᵖ} (g : j ⟶ j') : IsAffineHom B S hS (diagram.map g)
  /-- Every stage is quasi-separated. -/
  isAbsolutelyQuasiSeparated (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B S hS hZ (diagram.obj j)
  /-- Every stage is of finite type over `Spec ℤ`. -/
  isFiniteTypeOverIntegers (j : Iᵒᵖ) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ (diagram.obj j)))
  /-- The projections from `X` to the stages. -/
  π : (Functor.const Iᵒᵖ).obj X ⟶ diagram
  /-- They exhibit `X` as the limit of the system. -/
  isLimit : IsLimit (Cone.mk X π)

/-- **The conclusion of Stacks 07SU.** A presheaf on the big fppf site of `S` *has a
Noetherian approximation* when it is the limit of a directed inverse system of algebraic
spaces with affine transition morphisms, each quasi-separated and of finite type over
`Spec ℤ`.

Stacks 07SU asserts that every quasi-compact, quasi-separated algebraic space over
`Spec ℤ` has one, that is, that for `X` an algebraic space,
`AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS X` and
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS hZ X` imply this. That
implication is **not** proved in this development. -/
abbrev HasNoetherianApproximation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  Nonempty (NoetherianApproximation B S hS hZ X)

namespace NoetherianApproximation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The index set of a Noetherian approximation has cofiltered opposite, which is the shape
the inverse-limit machinery for algebraic spaces is stated for. -/
theorem isCofiltered_op (A : NoetherianApproximation B S hS hZ X) :
    letI := A.preorder; letI := A.nonempty; letI := A.isDirected
    IsCofiltered (A.I)ᵒᵖ := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  infer_instance

/-- A Noetherian approximation of `X` is a Noetherian approximation of any presheaf
isomorphic to `X`: the system is unchanged and the projections are composed with the
inverse of the isomorphism. -/
def ofIso (A : NoetherianApproximation B S hS hZ X) (e : X ≅ Y) :
    NoetherianApproximation B S hS hZ Y :=
  letI := A.preorder
  letI := A.nonempty
  letI := A.isDirected
  { I := A.I
    diagram := A.diagram
    isAlgebraicSpace := A.isAlgebraicSpace
    isAffineHom_map := A.isAffineHom_map
    isAbsolutelyQuasiSeparated := A.isAbsolutelyQuasiSeparated
    isFiniteTypeOverIntegers := A.isFiniteTypeOverIntegers
    π := (Functor.const _).map e.inv ≫ A.π
    isLimit := A.isLimit.ofIsoLimit (Cone.ext e (fun j => by simp)) }

/-- Transport of a Noetherian approximation along an isomorphism, as a statement about the
proposition. -/
theorem _root_.AlgebraicGeometry.Space.HasNoetherianApproximation.ofIso
    (h : HasNoetherianApproximation B S hS hZ X) (e : X ≅ Y) :
    HasNoetherianApproximation B S hS hZ Y :=
  h.elim fun A => ⟨A.ofIso e⟩

/-- **The base case.** An algebraic space which is already quasi-separated and of finite
type over `Spec ℤ` is its own Noetherian approximation: take the constant inverse system
over the one-element directed set. -/
noncomputable def const (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ X))) :
    NoetherianApproximation B S hS hZ X where
  I := PUnit.{u + 1}
  diagram := (Functor.const _).obj X
  isAlgebraicSpace _ := hX
  isAffineHom_map _ := isAffineHom_id X
  isAbsolutelyQuasiSeparated _ := hqs
  isFiniteTypeOverIntegers _ := hft
  π := 𝟙 _
  isLimit := isLimitConstCone _ X

end NoetherianApproximation

/-! ### Uniqueness of the quotient of a common presentation -/

/-- **Uniqueness of the quotient of an étale presentation.** Let `U` be an object of the big
fppf site of `S` and let `s, t : R ⟶ U` be a pair of morphisms in it. If two algebraic
spaces `X` and `X'` over `S` both receive a surjective étale morphism from `yoneda.obj U`
whose kernel pair is `(s, t)`, then there is an isomorphism `X ≅ X'` carrying the one atlas
to the other.

This is the step the proof of Stacks 07SU ends with: the limit `X' = lim X_i` of the
constructed system comes with a surjective étale atlas `V ⟶ X'` whose kernel pair is
identified with that of the given atlas `V ⟶ X`, and the two spaces are therefore the same.
It is an immediate consequence of Stacks 0262 (3), by which each of `X` and `X'` is the
coequalizer of `(s, t)` in fppf sheaves. -/
theorem exists_iso_of_common_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS} {s t : R ⟶ U}
    {f : yoneda.obj U ⟶ X} {f' : yoneda.obj U ⟶ X'}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hR' : IsPullback (yoneda.map s) (yoneda.map t) f' f')
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hsurj' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f')
    (hetale' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f') :
    ∃ e : X ≅ X', f ≫ e.hom = f' := by
  obtain ⟨hRsh, hUsh, hc⟩ := isCoequalizer_of_surjectiveEtale B S hS f s t hR hX hsurj hetale
  obtain ⟨hRsh', hUsh', hc'⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f' s t hR' hX' hsurj' hetale'
  set J := BigFppfOver.topology B S hS
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let FF : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  let FF' : Sheaf J (Type u) := ⟨X', hX'.isSheaf⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let ff : UF ⟶ FF := ⟨f⟩
  let ff' : UF ⟶ FF' := ⟨f'⟩
  have w : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hR.w
  have w' : sf ≫ ff' = tf ≫ ff' := Sheaf.hom_ext hR'.w
  obtain ⟨h1⟩ : Nonempty (IsColimit (Cofork.ofπ ff w)) := hc
  obtain ⟨h2⟩ : Nonempty (IsColimit (Cofork.ofπ ff' w')) := hc'
  refine ⟨(sheafToPresheaf J (Type u)).mapIso (h1.coconePointUniqueUpToIso h2), ?_⟩
  exact congrArg InducedCategory.Hom.hom
    (h1.comp_coconePointUniqueUpToIso_hom h2 WalkingParallelPair.one)

/-- **Uniqueness of the quotient of an étale presentation**, in the form the proof of Stacks
07SU uses it: the two kernel pairs need only be isomorphic as relations on `U`, not equal.

Here `f` and `f'` are surjective étale atlases of `X` and `X'` from the same object `U` of
the big fppf site of `S`, with kernel pairs `(s, t)` on `R` and `(s', t')` on `R'`, and `i`
is an isomorphism `R ≅ R'` carrying the one pair to the other. -/
theorem exists_iso_of_isomorphic_presentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R R' U : BigFppfOver B S hS}
    {s t : R ⟶ U} {s' t' : R' ⟶ U}
    {f : yoneda.obj U ⟶ X} {f' : yoneda.obj U ⟶ X'}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hR' : IsPullback (yoneda.map s') (yoneda.map t') f' f')
    (i : R ≅ R') (hs : i.hom ≫ s' = s) (ht : i.hom ≫ t' = t)
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hsurj' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f')
    (hetale' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f') :
    ∃ e : X ≅ X', f ≫ e.hom = f' := by
  refine exists_iso_of_common_presentation B S hS hR
    (hR'.of_iso' (yoneda.mapIso i) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp)
      (by simp)) hX hX' hsurj hetale hsurj' hetale'
  · simpa [← Functor.map_comp] using congrArg yoneda.map hs
  · simpa [← Functor.map_comp] using congrArg yoneda.map ht

end AlgebraicGeometry.Space

end
