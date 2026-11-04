module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Sections
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafDescent
public import StacksFrontier.Deformation.LiftsOfObjects.Action.PairTorsor

/-!
# The sections of a groupoid in algebraic spaces which are infinitesimally close to the unit

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, with unit
`e : U ⟶ R`, and let `U₀ ⊆ U` be a closed subspace.  Write `R₀ = s⁻¹(U₀) ⊆ R`, with projection
`s₀ : R₀ ⟶ U₀`, and let `i : U₀ ⟶ U` and `j : R₀ ⟶ R` be the two inclusions.  The unit carries
`U₀` into `R₀`, so it restricts to `e₀ : U₀ ⟶ R₀`, the unit of the restricted groupoid, and the
sections `δ` of `s` with `δ|_{U₀} = e₀` form the subset

`Γ₀ = {δ ∈ Γ | δ|_{U₀} = e₀}`

of the groupoid of sections `Γ` of [Stacks Project, Tag 0CKB].  This file builds `e₀` and `Γ₀`,
assembles the two sides of Equation [Stacks Project, Tag 0CKE] — the `𝒪_{U₀}`-module
homomorphisms `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` on the left, and `Γ₀` on the right, the latter related
chart by chart to the sheaf of lifts of [Stacks Project, Tag 0CK7] in the groupoid situation —
and proves that Equation [Stacks Project, Tag 0CKE] is a bijection, that is that every `δ ∈ Γ₀`
is `θ · e` for exactly one `θ`, when `U` is a first order thickening of `U₀`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictedSection`: the restriction
  `δ|_{U₀} : U₀ ⟶ R₀` of a section of the source, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictedUnit`: the unit `e₀ : U₀ ⟶ R₀` of the
  restricted groupoid, the factorization of `i ≫ e` through `R₀ = s⁻¹(U₀)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInfinitesimalSection`: the condition
  `δ|_{U₀} = e₀` cutting `Γ₀` out of `Γ`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSections`: the set `Γ₀`, the right
  hand side of Equation [Stacks Project, Tag 0CKE].
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionsHom`: the left hand side of
  Equation [Stacks Project, Tag 0CKE], the `𝒪_{U₀}`-linear maps
  `θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsActionSheaf`: the acting
  sheaf `SheafHom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U})` of [Stacks Project, Tag 061C], which is
  `AlgebraicGeometry.Space.liftActionSheaf` at the restricted data.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsLiftSheaf`: the sheaf of
  lifts of [Stacks Project, Tag 0CK7] in the groupoid situation, which is
  `AlgebraicGeometry.Space.liftsSubfunctor` at the restricted data.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionComp`: the composition of
  [Stacks Project, Tag 0CKC] restricted to `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference`: the difference
  of two elements of `Γ₀`, as an `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`, together with
  its additivity and the existence of a unique section with a prescribed difference from a
  given one.  This is [Stacks Project, Tag 0618] with Equation (0619) and
  [Stacks Project, Tag 04D0] in the groupoid situation; see the implementation notes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference.addAction`: the
  action `θ · δ` of [Stacks Project, Tag 0CK6] on `Γ₀`, the translate of `δ` by `θ` being the
  unique section whose difference from `δ` is `θ`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference.unitVAddEquiv`:
  Equation [Stacks Project, Tag 0CKE] itself, `θ ↦ θ · e`, bundled as a bijection.

## Main results

* `AlgebraicGeometry.Space.isPullback_subspaceInclusion_preimage`: the inverse image of a closed
  subspace along a morphism of algebraic spaces is the fibre product, so in particular
  `R₀ = U₀ ×_{U, s} R` (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_restrictedArrows`).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionCompHom_hom_app`: the composition formula
  of [Stacks Project, Tag 0CKC] at a point of a test scheme.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInfinitesimalSection_sectionComp`: `Γ₀` is
  closed under composition; with `isInfinitesimalSection_unitSection` this is the assertion of
  [Stacks Project, Tag 0CKB] that `Γ₀` is a subgroupoid of `Γ`, in the part not needing
  flatness.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictedUnit_comp_subspaceInclusion` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictedUnit_comp_restrictedSource`: the two
  equations characterizing `e₀`, that it is a factorization of `i ≫ e` through `j` and that it
  is a section of `s₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInfinitesimalSection_unitSection`: the unit is
  in `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInfinitesimalSection_iff_restrictedSection`:
  the membership condition of `Γ₀` is the equality `δ|_{U₀} = e₀` of the restrictions as
  morphisms `U₀ ⟶ R₀`, the two forms differing by the monomorphism `j`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.mem_infinitesimalSectionsLiftSheaf`: an element
  of `Γ₀` restricts on every étale chart of `U` to a section of the sheaf of lifts.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInfinitesimalSection_of_mem_liftSheaf`: the
  converse on a chart, that a section whose restriction to a chart is a lift agrees with the
  unit on the part of the chart lying in `U₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_infinitesimalSection_of_mem_liftSheaf`:
  a lift over a surjective étale chart of `U` whose two restrictions along a represented kernel
  pair of that chart agree is the restriction of exactly one element of `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSection_map_restrict` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_infinitesimalSection_of_sections`:
  **`Γ₀` is the set of global sections of the sheaf of lifts.**  The restrictions of an element
  of `Γ₀` to the étale charts of `U` are a compatible family of lifts, and every compatible
  family of lifts is the family of restrictions of exactly one element of `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFirstOrderThickening_restrictedArrows`:
  `R₀ ⊂ R` is a first order thickening as soon as `U₀ ⊂ U` is.
* `InfinitesimalSectionDifference.bijective_vadd_unitInfinitesimalSection` (in the namespace
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces`): **Equation [Stacks Project, Tag 0CKE]**.  The
  map `θ ↦ θ · e` is a bijection from the `𝒪_{U₀}`-linear maps `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` onto
  `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference.diff_vadd` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.InfinitesimalSectionDifference.eq_vadd`: the
  equation which characterizes `θ · δ`, that the difference of `δ` from `θ · δ` is `θ`.

## Implementation notes

**`R₀` is `s⁻¹(U₀)`, not `t⁻¹(U₀)`.** The Stacks project takes `U₀` to be `R`-invariant, so that
`s⁻¹(U₀) = t⁻¹(U₀)` and the choice is immaterial; invariance is not needed for anything in this
file and is not assumed. `R₀` is therefore the inverse image along the source,
`AlgebraicGeometry.Space.preimageSubspace` of the source morphism, whose projection to `U₀` is
`AlgebraicGeometry.Space.preimageProjection`, and the commutative square `j ≫ s = s₀ ≫ i` of the
two inclusions is `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`.

**Why `Γ₀` is a subtype of the sections and not a subfunctor.** The Stacks project describes `Γ₀`
as a subgroupoid of `Γ`, and `Γ` is a *set* of morphisms of algebraic spaces,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Section`. The membership condition `δ|_{U₀} = e₀` is
recorded as the equality `i ≫ δ = i ≫ e` of morphisms `U₀ ⟶ R`, which
`isInfinitesimalSection_iff_restrictedSection` proves equivalent to `δ|_{U₀} = e₀` as morphisms
`U₀ ⟶ R₀`, and which avoids having to transport along the factorization through `R₀` in every
statement.

**The two sides of Equation (0CKE) are built from the general lifting machinery.** The left hand
side is `AlgebraicGeometry.Space.liftActionSheaf` — the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of [Stacks Project, Tag 061C] — at `X ⊆ X'` equal to
`U₀ ⊆ U`, at `Y = R₀`, at `B = U₀` and at `a = e₀`, with `InfinitesimalSectionsHom` the type of
*global* `𝒪_{U₀}`-linear maps between the same two modules. The right hand side is
`AlgebraicGeometry.Space.liftsSubfunctor` at `X ⊆ X'` equal to `U₀ ⊆ U`, at `Y = R`, at `B = U`, at
`p = id_U`, at `q = s` and at `a = i ≫ e`; that is the shape [Stacks Project, Tag 0CK7] gives the
sheaf of lifts in the situation where the base is itself a thickening and the target is its base
change, since `R₀ = U₀ ×_{U, s} R` by construction.

**Equation (0CKE) is stated for a datum.** The bijection is stated for an
`InfinitesimalSectionDifference`: the `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which two
elements of `Γ₀` differ, which is [Stacks Project, Tag 0618] with Equation (0619), and the
existence of a unique element of `Γ₀` with a prescribed difference from a given one, which is
[Stacks Project, Tag 04D0].

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- The inclusion of a closed subspace of an algebraic space is a monomorphism. -/
theorem mono_subspaceInclusion {X : AlgebraicSpaces C S hS} (Z : ClosedSubspaces C S hS X.1) :
    Mono (subspaceInclusion C S hS X Z) := by
  apply (ObjectProperty.ι _).mono_of_mono_map
  show Mono Z.1.ι
  infer_instance

/-- **The inverse image of a closed subspace is the fibre product.**  For a morphism
`φ : X ⟶ X'` of algebraic spaces and a closed subspace `Z' ⊆ X'`, the square

```
φ⁻¹(Z') --→ X
   |         |
   p         φ
   ↓         ↓
  Z'  -----→ X'
```

whose horizontal arrows are the two inclusions and whose left vertical arrow is the projection
`p` is cartesian: `φ⁻¹(Z') = X ×_{X'} Z'`. -/
theorem isPullback_subspaceInclusion_preimage {X X' : AlgebraicSpaces C S hS} (φ : X ⟶ X')
    (Z' : ClosedSubspaces C S hS X'.1) :
    IsPullback (subspaceInclusion C S hS X (preimageSubspace C S hS φ Z'))
      (preimageProjection C S hS φ Z') φ (subspaceInclusion C S hS X' Z') := by
  have hrange : ∀ c : PullbackCone φ (subspaceInclusion C S hS X' Z'),
      Subfunctor.range c.fst.hom ≤ Z'.1.preimage φ.hom := by
    intro c T point hpoint
    obtain ⟨x, rfl⟩ := hpoint
    show φ.hom.app T (c.fst.hom.app T x) ∈ Z'.1.obj T
    have hx : φ.hom.app T (c.fst.hom.app T x) = (c.snd.hom.app T x).val :=
      congrArg (fun m : c.pt ⟶ X' => m.hom.app T x) c.condition
    rw [hx]
    exact (c.snd.hom.app T x).property
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (conormalEtaleRestrictionSquare C S hS φ Z') (fun c => ObjectProperty.homMk
      (Subfunctor.lift c.fst.hom (hrange c))) (fun c => ?_) (fun c => ?_) (fun c m hm _ => ?_))
  · exact ObjectProperty.hom_ext _ (Subfunctor.lift_ι c.fst.hom (hrange c))
  · apply ObjectProperty.hom_ext
    ext T x
    apply Subtype.ext
    exact congrArg (fun m : c.pt ⟶ X' => m.hom.app T x) c.condition
  · have := mono_subspaceInclusion C S hS (preimageSubspace C S hS φ Z')
    refine (cancel_mono (subspaceInclusion C S hS X (preimageSubspace C S hS φ Z'))).mp ?_
    rw [hm]
    exact (ObjectProperty.hom_ext _ (Subfunctor.lift_ι c.fst.hom (hrange c))).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)

/-! ### The unit of the restricted groupoid -/

/-- A morphism which is a section of the source evaluates to a point with the same source. -/
private theorem source_app_of_comp_eq_id {f : G.objects ⟶ G.arrows} (hf : f ≫ G.source = 𝟙 _)
    (T : (BigFppfOver C S hS)ᵒᵖ) (y : G.objects.obj.obj T) :
    G.source.hom.app T (f.hom.app T y) = y :=
  congrArg (fun m : G.objects ⟶ G.objects => m.hom.app T y) hf

/-- The image of `i ≫ f` lies in `s⁻¹(U₀)` for any section `f` of the source. -/
private theorem range_subspaceInclusion_comp_le_preimage {f : G.objects ⟶ G.arrows}
    (hf : f ≫ G.source = 𝟙 _) :
    Subfunctor.range (subspaceInclusion C S hS G.objects U₀ ≫ f).hom ≤
      U₀.1.preimage G.source.hom := by
  intro T point hpoint
  obtain ⟨x, rfl⟩ := hpoint
  change G.source.hom.app T (f.hom.app T x.val) ∈ U₀.1.obj T
  rw [source_app_of_comp_eq_id G hf]
  exact x.property

/-- **The unit carries `U₀` into `R₀ = s⁻¹(U₀)`:** the image of `i ≫ e` lies in the inverse image
of `U₀` along the source. -/
theorem range_subspaceInclusion_comp_identityArrow :
    Subfunctor.range (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom ≤
      U₀.1.preimage G.source.hom :=
  range_subspaceInclusion_comp_le_preimage G U₀ (identityArrow_comp_source G)

/-- **The unit `e₀ : U₀ ⟶ R₀` of the restricted groupoid.**  The factorization of `i ≫ e`
through the closed subspace `R₀ = s⁻¹(U₀)` of `R` provided by
`range_subspaceInclusion_comp_identityArrow`. -/
def restrictedUnit :
    (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS) :=
  ObjectProperty.homMk (Subfunctor.lift
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom
    (range_subspaceInclusion_comp_identityArrow G U₀))

/-- **`e₀` is a factorization of `i ≫ e`:** composing it with the inclusion `j : R₀ ⟶ R` gives
the restriction of the unit to `U₀`. -/
theorem restrictedUnit_comp_subspaceInclusion :
    restrictedUnit G U₀ ≫
        subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) =
      subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G :=
  ObjectProperty.hom_ext _ (Subfunctor.lift_ι
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom
    (range_subspaceInclusion_comp_identityArrow G U₀))

/-- **`e₀` is a section of the restricted source `s₀ : R₀ ⟶ U₀`.** -/
theorem restrictedUnit_comp_restrictedSource :
    restrictedUnit G U₀ ≫ preimageProjection C S hS G.source U₀ = 𝟙 _ := by
  have hmono := mono_subspaceInclusion C S hS U₀
  rw [← cancel_mono (subspaceInclusion C S hS G.objects U₀), Category.assoc,
    ← conormalEtaleRestrictionSquare C S hS G.source U₀, ← Category.assoc,
    restrictedUnit_comp_subspaceInclusion, Category.assoc, identityArrow_comp_source,
    Category.comp_id, Category.id_comp]

/-- **`R₀ = U₀ ×_{U, s} R`.**  The square of the two inclusions, the source `s` and the
restricted source `s₀` is cartesian. -/
theorem isPullback_restrictedArrows :
    IsPullback
      (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
      (preimageProjection C S hS G.source U₀) G.source
      (subspaceInclusion C S hS G.objects U₀) :=
  isPullback_subspaceInclusion_preimage C S hS G.source U₀

/-! ### The restriction of a section to `U₀` -/

/-- **Every section of the source carries `U₀` into `R₀ = s⁻¹(U₀)`:** for a section `δ` of `s`, the
image of `i ≫ δ` lies in the inverse image of `U₀` along the source. -/
theorem range_subspaceInclusion_comp_section (δ : Section G) :
    Subfunctor.range (subspaceInclusion C S hS G.objects U₀ ≫ δ.1).hom ≤
      U₀.1.preimage G.source.hom :=
  range_subspaceInclusion_comp_le_preimage G U₀ δ.2

/-- **The restriction `δ|_{U₀} : U₀ ⟶ R₀` of a section of the source**, the factorization of
`i ≫ δ` through the closed subspace `R₀ = s⁻¹(U₀)` of `R`. -/
def restrictedSection (δ : Section G) :
    (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
        (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS) :=
  ObjectProperty.homMk (Subfunctor.lift
    (subspaceInclusion C S hS G.objects U₀ ≫ δ.1).hom
    (range_subspaceInclusion_comp_section G U₀ δ))

/-- `δ|_{U₀}` is a factorization of `i ≫ δ` through the inclusion `j : R₀ ⟶ R`. -/
theorem restrictedSection_comp_subspaceInclusion (δ : Section G) :
    restrictedSection G U₀ δ ≫
        subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) =
      subspaceInclusion C S hS G.objects U₀ ≫ δ.1 :=
  ObjectProperty.hom_ext _ (Subfunctor.lift_ι
    (subspaceInclusion C S hS G.objects U₀ ≫ δ.1).hom
    (range_subspaceInclusion_comp_section G U₀ δ))

/-! ### The sections infinitesimally close to the unit -/

/-- **The membership condition of `Γ₀`:** a section `δ` of the source is *infinitesimally close
to the unit along `U₀`* when its restriction to `U₀` is the restriction of the unit, that is
when `δ|_{U₀} = e₀`.  Written as an equality of morphisms `U₀ ⟶ R`, which is equivalent to the
equality of the restrictions `U₀ ⟶ R₀` by `isInfinitesimalSection_iff_restrictedSection`,
because the inclusion `j : R₀ ⟶ R` is a monomorphism. -/
def IsInfinitesimalSection (δ : Section G) : Prop :=
  subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
    subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G

/-- **The set `Γ₀` of [Stacks Project, Tag 0CKB]:** the sections of the source which agree with
the unit on `U₀`.  This is the right hand side of Equation [Stacks Project, Tag 0CKE]. -/
def InfinitesimalSections :=
  {δ : Section G // IsInfinitesimalSection G U₀ δ}

/-- The unit `e` is a section of the source. -/
def unitSection : Section G :=
  ⟨identityArrow G, identityArrow_comp_source G⟩

/-- The unit `e₀` of the restricted groupoid is the restriction of the unit section. -/
theorem restrictedUnit_eq_restrictedSection :
    restrictedUnit G U₀ = restrictedSection G U₀ (unitSection G) := rfl

/-- **The unit lies in `Γ₀`.** -/
theorem isInfinitesimalSection_unitSection :
    IsInfinitesimalSection G U₀ (unitSection G) := rfl

/-- `Γ₀` is not empty: it contains the unit. -/
def unitInfinitesimalSection : InfinitesimalSections G U₀ :=
  ⟨unitSection G, isInfinitesimalSection_unitSection G U₀⟩

/-- **The membership condition of `Γ₀` is the equality of the restrictions to `U₀` as
morphisms into `R₀`.**  The two forms differ by composition with the inclusion `j : R₀ ⟶ R`,
which is a monomorphism. -/
theorem isInfinitesimalSection_iff_restrictedSection (δ : Section G) :
    IsInfinitesimalSection G U₀ δ ↔ restrictedSection G U₀ δ = restrictedUnit G U₀ := by
  have hmono := mono_subspaceInclusion C S hS (preimageSubspace C S hS G.source U₀)
  constructor
  · intro h
    rw [← cancel_mono
      (subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀)),
      restrictedSection_comp_subspaceInclusion, restrictedUnit_comp_subspaceInclusion]
    exact h
  · intro h
    show subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
      subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G
    rw [← restrictedSection_comp_subspaceInclusion G U₀ δ, h,
      restrictedUnit_comp_subspaceInclusion]

/-- An element of `Γ₀` agrees with the unit of the restricted groupoid after factorization
through `R₀`: its restriction to `U₀` is `e₀` followed by the inclusion of `R₀`. -/
theorem comp_eq_restrictedUnit_comp {δ : Section G} (hδ : IsInfinitesimalSection G U₀ δ) :
    subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
      restrictedUnit G U₀ ≫
        subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) :=
  hδ.trans (restrictedUnit_comp_subspaceInclusion G U₀).symm

/-! ### `Γ₀` is closed under composition -/

/-- The composite of two arrows of a groupoid in algebraic spaces at a point of a test scheme,
read in the pointwise groupoid: the value of the composition morphism on a composable pair. -/
theorem compose_congr (T : (BigFppfOver C S hS)ᵒᵖ) {a a' b b' : G.arrows.obj.obj T}
    (ha : a = a') (hb : b = b')
    (h : G.source.hom.app T a = G.target.hom.app T b)
    (h' : G.source.hom.app T a' = G.target.hom.app T b') :
    G.toGroupoidInFunctors.compose T a b h = G.toGroupoidInFunctors.compose T a' b' h' := by
  subst ha
  subst hb
  rfl

/-- **The identity arrow composed with itself is the identity arrow**, at every point of every
test scheme: in the pointwise groupoid the composite of `𝟙` with `𝟙` is `𝟙`. -/
theorem compose_identity_identity (T : (BigFppfOver C S hS)ᵒᵖ) (z : G.objects.obj.obj T)
    (h : G.source.hom.app T (G.toGroupoidInFunctors.identity T z) =
      G.target.hom.app T (G.toGroupoidInFunctors.identity T z)) :
    G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.identity T z)
        (G.toGroupoidInFunctors.identity T z) h = G.toGroupoidInFunctors.identity T z := by
  have key := G.toGroupoidInFunctors.evaluationArrowEquiv_comp T
    (x := (show G.toGroupoidInFunctors.Evaluation T from z))
    (y := (show G.toGroupoidInFunctors.Evaluation T from z))
    (z := (show G.toGroupoidInFunctors.Evaluation T from z))
    (𝟙 (show G.toGroupoidInFunctors.Evaluation T from z))
    (𝟙 (show G.toGroupoidInFunctors.Evaluation T from z))
  rw [Category.comp_id] at key
  exact key.symm

/-- **The composition formula of [Stacks Project, Tag 0CKC] at a point.**  Over a test scheme,
the composite `δ₁ ∘ δ₂` of two sections sends a point `y` of the object space to the groupoid
composite of the arrow `δ₂` assigns to `y` with the arrow `δ₁` assigns to the target of that
arrow. -/
theorem sectionCompHom_hom_app (δ₁ δ₂ : Section G) (T : (BigFppfOver C S hS)ᵒᵖ)
    (y : G.objects.obj.obj T)
    (h : G.source.hom.app T (δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T y))) =
      G.target.hom.app T (δ₂.1.hom.app T y)) :
    (sectionCompHom G δ₁ δ₂).hom.app T y =
      G.toGroupoidInFunctors.compose T
        (δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T y))) (δ₂.1.hom.app T y) h := by
  have hh : δ₁.1.hom ≫ G.source.hom = 𝟙 G.objects.obj := congrArg (fun f => f.hom) δ₁.2
  let q : G.objects.obj ⟶
      Deformation.composableArrows G.objects.obj G.arrows.obj G.source.hom G.target.hom :=
    { app := fun T => ↾ fun x => ⟨
        (δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T x)), δ₂.1.hom.app T x),
        by rw [source_app_of_comp_eq_id G δ₁.2]⟩
      naturality := by
        intro X Y f
        ext x
        simp [Deformation.composableArrows] }
  have hpair :
      pullback.lift (δ₂.1.hom ≫ G.target.hom ≫ δ₁.1.hom) δ₂.1.hom
          (by simp [Category.assoc, hh]) =
        q ≫ composableToPullback G.source.hom G.target.hom := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, composableToPullback]
      ext T x
      rfl
    · simp only [pullback.lift_snd, Category.assoc, composableToPullback]
      ext T x
      rfl
  have happ : (sectionCompHom G δ₁ δ₂).hom.app T y =
      (composableToPullback G.source.hom G.target.hom ≫ G.comp.hom).app T (q.app T y) := by
    show G.comp.hom.app T
        ((pullback.lift (δ₂.1.hom ≫ G.target.hom ≫ δ₁.1.hom) δ₂.1.hom
          (by simp [Category.assoc, hh])).app T y) =
      G.comp.hom.app T
        ((composableToPullback G.source.hom G.target.hom).app T (q.app T y))
    congr 1
    exact congrArg (fun f => f.app T y) hpair
  rw [happ]
  rfl

/-- **`Γ₀` is closed under the composition of [Stacks Project, Tag 0CKC].**  If two sections
agree with the unit on `U₀` then so does their composite.

With `isInfinitesimalSection_unitSection` this is the assertion of [Stacks Project, Tag 0CKB]
that `Γ₀` is a subgroupoid of `Γ`, in the part that does not need flatness: a submonoid. -/
theorem isInfinitesimalSection_sectionComp {δ₁ δ₂ : Section G}
    (h₁ : IsInfinitesimalSection G U₀ δ₁) (h₂ : IsInfinitesimalSection G U₀ δ₂) :
    IsInfinitesimalSection G U₀ (sectionComp G δ₁ δ₂) := by
  have hres : ∀ {δ : Section G}, IsInfinitesimalSection G U₀ δ →
      ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (x : U₀.1.toFunctor.obj T),
        δ.1.hom.app T x.val = (identityArrow G).hom.app T x.val := by
    intro δ hδ T x
    exact congrArg
      (fun m : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶ G.arrows => m.hom.app T x) hδ
  apply ObjectProperty.hom_ext
  ext T x
  have hunitSrc : G.source.hom.app T ((identityArrow G).hom.app T x.val) = x.val :=
    source_app_of_comp_eq_id G (identityArrow_comp_source G) T x.val
  have hunitTgt : G.target.hom.app T ((identityArrow G).hom.app T x.val) = x.val :=
    congrArg (fun m : G.objects ⟶ G.objects => m.hom.app T x.val) (identityArrow_comp_target G)
  have hide : (identityArrow G).hom.app T x.val =
      G.toGroupoidInFunctors.identity T x.val := identityArrow_hom_app G T x.val
  have hta : G.target.hom.app T (δ₂.1.hom.app T x.val) = x.val := by
    rw [hres h₂ T x]
    exact hunitTgt
  have hb : δ₂.1.hom.app T x.val = G.toGroupoidInFunctors.identity T x.val := by
    rw [hres h₂ T x]
    exact hide
  have ha : δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T x.val)) =
      G.toGroupoidInFunctors.identity T x.val := by
    rw [hta, hres h₁ T x]
    exact hide
  have hid : G.source.hom.app T (G.toGroupoidInFunctors.identity T x.val) =
      G.target.hom.app T (G.toGroupoidInFunctors.identity T x.val) := by
    rw [← hide, hunitSrc, hunitTgt]
  show (sectionCompHom G δ₁ δ₂).hom.app T x.val = (identityArrow G).hom.app T x.val
  rw [sectionCompHom_hom_app G δ₁ δ₂ T x.val (source_app_of_comp_eq_id G δ₁.2 T _),
    compose_congr G T ha hb (source_app_of_comp_eq_id G δ₁.2 T _) hid,
    compose_identity_identity G T x.val hid]
  exact hide.symm

/-- **Composition on `Γ₀`:** the composition of [Stacks Project, Tag 0CKC] restricted to the
sections infinitesimally close to the unit, which lands there again by
`isInfinitesimalSection_sectionComp`. -/
def infinitesimalSectionComp (δ₁ δ₂ : InfinitesimalSections G U₀) :
    InfinitesimalSections G U₀ :=
  ⟨sectionComp G δ₁.1 δ₂.1, isInfinitesimalSection_sectionComp G U₀ δ₁.2 δ₂.2⟩

/-! ### The two sides of Equation (0CKE) -/

/-- **The left hand side of Equation [Stacks Project, Tag 0CKE]:** the `𝒪_{U₀}`-linear maps
`θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`, from the inverse image along `e₀` of the sheaf of differentials
of [Stacks Project, Tag 04CT] of the restricted source `s₀ : R₀ ⟶ U₀` to the conormal module of
[Stacks Project, Tag 04CN] of `U₀` in `U`. -/
abbrev InfinitesimalSectionsHom :=
  (modulePullback C S hS (restrictedUnit G U₀)).obj
      (sheafOfDifferentials C S hS (preimageProjection C S hS G.source U₀)) ⟶
    conormalModule C S hS G.objects U₀

/-- **The acting sheaf of [Stacks Project, Tag 061C] in the groupoid situation:**
`SheafHom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U})`, the internal Hom of the two modules whose global
morphisms are `InfinitesimalSectionsHom`. -/
def infinitesimalSectionsActionSheaf : Modules C S hS U₀.1.toFunctor U₀.2.1 :=
  liftActionSheaf C S hS U₀ (preimageProjection C S hS G.source U₀) (restrictedUnit G U₀)

/-- **The sheaf of lifts of [Stacks Project, Tag 0CK7] in the groupoid situation:** on an étale
chart `U'` of `U` its sections are the morphisms `U' ⟶ R` over `U` — over `s`, that is — whose
restriction to `U₀ ×_U U'` is the restriction of `i ≫ e`. -/
def infinitesimalSectionsLiftSheaf :
    Subfunctor ((Space.SmallEtale.toOver C S hS G.objects.1).op ⋙ G.arrows.1) :=
  liftsSubfunctor C S hS (𝟙 G.objects) G.source
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom

/-! ### `Γ₀` and the sheaf of lifts -/

/-- An element of `Γ₀` is a section of the source whose restriction to `U₀` is that of the unit,
as morphisms of functors. -/
private theorem hom_facts_of_isInfinitesimalSection {δ : Section G}
    (hδ : IsInfinitesimalSection G U₀ δ) :
    δ.1.hom ≫ G.source.hom = (𝟙 G.objects : G.objects ⟶ G.objects).hom ∧
      U₀.1.ι ≫ δ.1.hom = (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom :=
  ⟨congrArg (fun m : G.objects ⟶ G.objects => m.hom) δ.2,
    congrArg (fun m : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶ G.arrows =>
      m.hom) hδ⟩

/-- Membership in the sheaf of lifts of the family `α`, unfolded to a chart lift. -/
private theorem isChartLift_of_mem_infinitesimalSectionsLiftSheaf
    {U' : Space.SmallEtale C S hS G.objects.1}
    {α : yoneda.obj ((Space.SmallEtale.toOver C S hS G.objects.1).obj U') ⟶ G.arrows.1}
    (h : yonedaEquiv α ∈ (infinitesimalSectionsLiftSheaf G U₀).obj (op U')) :
    IsChartLift C S hS (𝟙 G.objects) G.source
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom U' α := by
  have h' : IsChartLift C S hS (𝟙 G.objects) G.source
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom U'
      (yonedaEquiv.symm (yonedaEquiv α)) := h
  rwa [Equiv.symm_apply_apply] at h'

/-- **An element of `Γ₀` restricts on every étale chart of `U` to a section of the sheaf of
lifts.** -/
theorem mem_infinitesimalSectionsLiftSheaf {δ : Section G}
    (hδ : IsInfinitesimalSection G U₀ δ) (U' : Space.SmallEtale C S hS G.objects.1) :
    yonedaEquiv (U'.1.hom ≫ δ.1.hom) ∈
      (infinitesimalSectionsLiftSheaf G U₀).obj (op U') := by
  show IsChartLift C S hS (𝟙 G.objects) G.source
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom U'
    (yonedaEquiv.symm (yonedaEquiv (U'.1.hom ≫ δ.1.hom)))
  rw [Equiv.symm_apply_apply]
  obtain ⟨hsec, hres⟩ := hom_facts_of_isInfinitesimalSection G U₀ hδ
  refine ⟨?_, fun W k t hkt => ?_⟩
  · rw [Category.assoc, hsec]
  · rw [← Category.assoc, hkt, Category.assoc, hres]

/-- **The converse on a single chart.**  If the restriction of a section `δ` to an étale chart
`U'` of `U` is a lift, then `δ` agrees with the unit on every point of the chart which lies in
`U₀`. -/
theorem isInfinitesimalSection_of_mem_liftSheaf (δ : Section G)
    (U' : Space.SmallEtale C S hS G.objects.1)
    (h : yonedaEquiv (U'.1.hom ≫ δ.1.hom) ∈ (infinitesimalSectionsLiftSheaf G U₀).obj (op U'))
    (W : BigFppfOver C S hS) (k : W ⟶ (Space.SmallEtale.toOver C S hS G.objects.1).obj U')
    (x : yoneda.obj W ⟶ U₀.1.toFunctor)
    (hkx : yoneda.map k ≫ U'.1.hom = x ≫ U₀.1.ι) :
    yoneda.map k ≫ U'.1.hom ≫ δ.1.hom = x ≫ U₀.1.ι ≫ (identityArrow G).hom := by
  exact (isChartLift_of_mem_infinitesimalSectionsLiftSheaf G U₀ h).2 W k x hkx

/-- **A lift over a surjective étale chart of `U` comes from exactly one element of `Γ₀`.**  Let
`U₁` be an étale chart of `U` whose structure morphism is surjective, so that `U₁` is an atlas,
and let `α : U₁ ⟶ R` be a section of the sheaf of lifts over `U₁` whose two restrictions along
any represented kernel pair of the atlas agree.  Then `α` is the restriction to `U₁` of exactly
one element of `Γ₀`. -/
theorem existsUnique_infinitesimalSection_of_mem_liftSheaf
    (U₁ : Space.SmallEtale C S hS G.objects.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS))) U₁.1.hom)
    (α : yoneda.obj ((Space.SmallEtale.toOver C S hS G.objects.1).obj U₁) ⟶ G.arrows.1)
    (hα : yonedaEquiv α ∈ (infinitesimalSectionsLiftSheaf G U₀).obj (op U₁))
    (hinv : ∀ (R' : BigFppfOver C S hS)
      (s t : R' ⟶ (Space.SmallEtale.toOver C S hS G.objects.1).obj U₁),
      IsPullback (yoneda.map s) (yoneda.map t) U₁.1.hom U₁.1.hom →
        yoneda.map s ≫ α = yoneda.map t ≫ α) :
    ∃! δ : InfinitesimalSections G U₀, U₁.1.hom ≫ δ.1.1.hom = α := by
  obtain ⟨a', ⟨hchart, hsrc, hres⟩, huniq⟩ :=
    Space.existsUnique_hom_of_isChartLift_atlas C S hS (𝟙 G.objects) G.source
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom U₁ hsurj α
      (isChartLift_of_mem_infinitesimalSectionsLiftSheaf G U₀ hα) hinv
  refine ⟨⟨⟨ObjectProperty.homMk a', ObjectProperty.hom_ext _ hsrc⟩,
    ObjectProperty.hom_ext _ hres⟩, hchart, fun ε hε => ?_⟩
  obtain ⟨hεsrc, hεres⟩ := hom_facts_of_isInfinitesimalSection G U₀ ε.2
  exact Subtype.ext (Subtype.ext
    (ObjectProperty.hom_ext _ (huniq ε.1.1.hom ⟨hε, hεsrc, hεres⟩)))

/-- **The restrictions of an element of `Γ₀` to the étale charts of `U` are compatible with
restriction**: they are the restrictions of one morphism `U ⟶ R`. -/
theorem infinitesimalSection_map_restrict (δ : InfinitesimalSections G U₀)
    {W V : Space.SmallEtale C S hS G.objects.1} (m : V ⟶ W) :
    G.arrows.1.map ((Space.SmallEtale.toOver C S hS G.objects.1).map m).op
        (yonedaEquiv (W.1.hom ≫ δ.1.1.hom)) =
      yonedaEquiv (V.1.hom ≫ δ.1.1.hom) := by
  have hw : yoneda.map ((Space.SmallEtale.toOver C S hS G.objects.1).map m) ≫ W.1.hom =
      V.1.hom := CostructuredArrow.w _
  rw [yonedaEquiv_naturality]
  refine congrArg _ ?_
  rw [← Category.assoc, hw]

/-- **`Γ₀` is the set of global sections of the sheaf of lifts.**  A compatible family of lifts
over every étale chart of `U` — a global section of `infinitesimalSectionsLiftSheaf` — is the
family of restrictions of exactly one element of `Γ₀`. -/
theorem existsUnique_infinitesimalSection_of_sections
    (α : (infinitesimalSectionsLiftSheaf G U₀).toFunctor.sections) :
    ∃! δ : InfinitesimalSections G U₀,
      ∀ W : Space.SmallEtale C S hS G.objects.1,
        yonedaEquiv (W.1.hom ≫ δ.1.1.hom) = (α.1 (op W)).1 := by
  set β : ∀ W : Space.SmallEtale C S hS G.objects.1,
      yoneda.obj ((Space.SmallEtale.toOver C S hS G.objects.1).obj W) ⟶ G.arrows.1 :=
    fun W => yonedaEquiv.symm ((α.1 (op W)).1 :
      G.arrows.1.obj (op ((Space.SmallEtale.toOver C S hS G.objects.1).obj W))) with hβ
  have hβapp : ∀ W : Space.SmallEtale C S hS G.objects.1,
      yonedaEquiv (β W) = (α.1 (op W)).1 := fun W => Equiv.apply_symm_apply _ _
  have hcompat : ∀ {W V : Space.SmallEtale C S hS G.objects.1} (m : V ⟶ W),
      yoneda.map ((Space.SmallEtale.toOver C S hS G.objects.1).map m) ≫ β W = β V := by
    intro W V m
    have hα : G.arrows.1.map
        ((Space.SmallEtale.toOver C S hS G.objects.1).map m).op (α.1 (op W)).1 =
        (α.1 (op V)).1 := Subtype.ext_iff.1 (α.2 m.op)
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality, hβapp, hα, hβapp]
  obtain ⟨a', ⟨hall, hsrc, hres⟩, huniq⟩ :=
    Space.existsUnique_hom_of_isChartLift_family C S hS (𝟙 G.objects) G.source
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom β
      (fun W => (α.1 (op W)).2) hcompat
  refine ⟨⟨⟨ObjectProperty.homMk a', ObjectProperty.hom_ext _ hsrc⟩,
    ObjectProperty.hom_ext _ hres⟩, fun W => ?_, fun ε hε => ?_⟩
  · exact (congrArg yonedaEquiv (hall W)).trans (hβapp W)
  · obtain ⟨hεsrc, hεres⟩ := hom_facts_of_isInfinitesimalSection G U₀ ε.2
    refine Subtype.ext (Subtype.ext (ObjectProperty.hom_ext _
      (huniq ε.1.1.hom ⟨fun W => ?_, hεsrc, hεres⟩)))
    refine yonedaEquiv.injective ?_
    rw [hε W, hβapp]

/-! ### Equation (0CKE) -/

/-- **`R₀ = s⁻¹(U₀)` is a first order thickening of `R`** as soon as `U₀ ⊂ U` is one. -/
theorem isFirstOrderThickening_restrictedArrows
    (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1) :
    IsFirstOrderThickening C S hS G.arrows (preimageSubspace C S hS G.source U₀).1 :=
  isFirstOrderThickening_preimage C S hS U₀.1 G.source hU₀

/-- **The difference of two sections infinitesimally close to the unit.**  For a first order
thickening `U₀ ⊂ U`, two elements `δ₁, δ₂` of `Γ₀` differ by an `𝒪_{U₀}`-linear map
`e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`; the difference is additive along a chain of three sections, and
every linear map is the difference of exactly one section from a given one. -/
structure InfinitesimalSectionDifference where
  /-- `U` is a first order thickening of `U₀`. -/
  firstOrder : IsFirstOrderThickening C S hS G.objects U₀.1
  /-- The `𝒪_{U₀}`-linear map `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` by which two sections of `Γ₀`
  differ. -/
  diff : InfinitesimalSections G U₀ → InfinitesimalSections G U₀ →
    InfinitesimalSectionsHom G U₀
  /-- A section does not differ from itself. -/
  diff_self : ∀ δ, diff δ δ = 0
  /-- The differences along a chain of three sections add up. -/
  diff_add_diff : ∀ δ₁ δ₂ δ₃, diff δ₁ δ₂ + diff δ₂ δ₃ = diff δ₁ δ₃
  /-- Every `𝒪_{U₀}`-linear map is the difference from a given section of exactly one
  section. -/
  existsUnique_diff : ∀ (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀),
    ∃! ε : InfinitesimalSections G U₀, diff δ ε = θ

namespace InfinitesimalSectionDifference

variable {G U₀} (h : InfinitesimalSectionDifference G U₀)

/-- Replacing the second member of a pair of sections of `Γ₀` by the linear map by which the
two differ is a bijection: a section is determined by its difference from a given one, and
every linear map occurs as such a difference. -/
noncomputable def diffPairEquiv :
    (InfinitesimalSections G U₀ × InfinitesimalSections G U₀) ≃
      (InfinitesimalSections G U₀ × InfinitesimalSectionsHom G U₀) where
  toFun p := (p.1, h.diff p.1 p.2)
  invFun p := (p.1, (h.existsUnique_diff p.1 p.2).exists.choose)
  left_inv p :=
    Prod.ext rfl ((h.existsUnique_diff p.1 (h.diff p.1 p.2)).unique
      (h.existsUnique_diff p.1 (h.diff p.1 p.2)).exists.choose_spec rfl)
  right_inv p := Prod.ext rfl (h.existsUnique_diff p.1 p.2).exists.choose_spec

/-- **The action `θ · δ` of the `𝒪_{U₀}`-linear maps on `Γ₀`:** the translate of `δ` by `θ` is
the unique section of `Γ₀` whose difference from `δ` is `θ`. -/
@[instance_reducible]
noncomputable def addAction :
    AddAction (InfinitesimalSectionsHom G U₀) (InfinitesimalSections G U₀) :=
  Deformation.addActionOfPairEquiv h.diffPairEquiv (fun _ _ => rfl) h.diff_self h.diff_add_diff

/-- The difference of `δ` from its translate `θ · δ` is `θ`. -/
theorem diff_vadd (δ : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀) :
    letI := h.addAction
    h.diff δ (θ +ᵥ δ) = θ :=
  Deformation.pairEquiv_inverse_difference h.diffPairEquiv (fun _ _ => rfl) δ θ

/-- A section of `Γ₀` whose difference from `δ` is `θ` is the translate `θ · δ`. -/
theorem eq_vadd (δ ε : InfinitesimalSections G U₀) (θ : InfinitesimalSectionsHom G U₀)
    (hd : h.diff δ ε = θ) :
    letI := h.addAction
    ε = θ +ᵥ δ :=
  let := h.addAction
  (h.existsUnique_diff δ θ).unique hd (h.diff_vadd δ θ)

/-- **Translation of the unit is a bijection from the `𝒪_{U₀}`-linear maps
`θ : e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` onto the sections `Γ₀` of the source which agree with the unit on
`U₀`:** every `δ ∈ Γ₀` is `θ · e` for exactly one `θ`.

This holds for an arbitrary datum `h`; Equation [Stacks Project, Tag 0CKE] is the case of the
canonical datum of a first order thickening,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.bijective_vadd_unitInfinitesimalSection`. -/
theorem bijective_vadd_unitInfinitesimalSection :
    letI := h.addAction
    Function.Bijective
      (fun θ : InfinitesimalSectionsHom G U₀ => θ +ᵥ unitInfinitesimalSection G U₀) :=
  Deformation.addActionOfPairEquiv_pointwiseBijective h.diffPairEquiv (fun _ _ => rfl)
    (unitInfinitesimalSection G U₀)

/-- **The bijection `θ ↦ θ · e`** from the `𝒪_{U₀}`-linear maps `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` to
the sections `Γ₀` infinitesimally close to the unit, bundled with its inverse, for an arbitrary
datum `h`.

Equation [Stacks Project, Tag 0CKE] is the case of the canonical datum of a first order thickening,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv`. -/
noncomputable def unitVAddEquiv :
    InfinitesimalSectionsHom G U₀ ≃ InfinitesimalSections G U₀ :=
  letI := h.addAction
  Equiv.ofBijective
    (fun θ : InfinitesimalSectionsHom G U₀ => θ +ᵥ unitInfinitesimalSection G U₀)
    h.bijective_vadd_unitInfinitesimalSection

/-- The bijection of Equation (0CKE) sends `θ` to `θ · e`. -/
theorem unitVAddEquiv_apply (θ : InfinitesimalSectionsHom G U₀) :
    letI := h.addAction
    h.unitVAddEquiv θ = θ +ᵥ unitInfinitesimalSection G U₀ := rfl

/-- The inverse of the bijection of Equation (0CKE) sends `δ` to its difference from the
unit. -/
theorem unitVAddEquiv_symm_apply (δ : InfinitesimalSections G U₀) :
    h.unitVAddEquiv.symm δ = h.diff (unitInfinitesimalSection G U₀) δ :=
  (h.unitVAddEquiv.symm_apply_eq).2
    (h.eq_vadd (unitInfinitesimalSection G U₀) δ _ rfl)

/-- The bijection of Equation (0CKE) sends the zero map to the unit. -/
@[simp] theorem unitVAddEquiv_zero :
    h.unitVAddEquiv 0 = unitInfinitesimalSection G U₀ :=
  let := h.addAction
  zero_vadd (InfinitesimalSectionsHom G U₀) (unitInfinitesimalSection G U₀)

end InfinitesimalSectionDifference

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
