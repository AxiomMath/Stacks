module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsHom
public import StacksFrontier.CategoryTheory.Sites.YonedaRepresentableMorphism

/-!
# Étale coverings and restriction of scalars (Stacks 05YD)

Let `S` be a scheme contained in a big fppf site, let `X' → X → Z → Q` be morphisms of algebraic
spaces over `S` — the source writes the base `Q` as `B`, a name that here belongs to the site —
and let `Res_{Z/Q}(X)` be the restriction of scalars of Stacks 05YA. Stacks 05YD asserts, for
`X' → X` étale and `Z → Q` finite locally free, that

```text
Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)
```

is representable by algebraic spaces and étale, and that it is surjective when `X' → X` is.

## The shape of the argument

The source proves all three assertions by computing the fibre of the map at a scheme-valued
point. A point `ξ` of `Res_{Z/Q}(X)` over a scheme `U` is a pair `(a, b)` of Stacks 05Y9: a
morphism `a : U ⟶ Q` and a morphism `b : Z_U = U ×_{a, Q} Z ⟶ X` over `Z`. Setting
`W = Z_U ×_{b, X} X'`, the fibre product

```text
h_U ×_{ξ, Res_{Z/Q}(X)} Res_{Z/Q}(X')
```

is the functor of sections of `W ⟶ Z_U` over `U`, which is the functor `F` of Stacks 05XR; and
`W ⟶ Z_U ⟶ U` satisfies the hypotheses of Stacks 05XR because they are the hypotheses on
`X' ⟶ X` and `Z ⟶ Q` base changed. The first two assertions are then Stacks 05XR and the third
is Stacks 05XQ.

That identification of the fibre is what this file proves, and it is proved in the form that
the functor of sections *is* a restriction of scalars again, namely `Res_{Z_U/U}(W)`: a section
of `W_T → (Z_U)_T` over `T/U` is the same thing as a morphism `T ⟶ U` together with a pair of
`Res_{Z/Q}(X')` over `T` whose postcomposition with `g` is the base change of `(a, b)`. The
comparison morphism is built out of the universal property of the fibre product, so it is
natural by construction, and it is shown to be an isomorphism by checking at each `T` that it is
injective and surjective; the two directions are
`AlgebraicGeometry.Space.RestrictionPair.ofFibrePair` and
`AlgebraicGeometry.Space.RestrictionPair.toFibrePair`, which are mutually inverse.

## What is carried as a hypothesis

Neither of the two inputs the three theorems below name is missing any more. The main assertion
of Stacks 05XR — that the functor of sections is an algebraic space étale over `U` — is the
theorem `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`, and Stacks 05XQ in the form
these proofs use it is `AlgebraicGeometry.Space.isFibreSectionsSurjective`; the base-change
stability of "étale" is `AlgebraicGeometry.Space.isEtale_of_isPullback`, Stacks 03FU.

They are carried below as the explicit hypotheses
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` and
`AlgebraicGeometry.Space.IsFibreSectionsSurjective` only because the three theorems sit upstream
of both proofs in the import graph: the finiteness input from Stacks 03ZU that both need lives in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartComparisonAssembly.lean`, which already imports this
file. Each hypothesis is premised on the hypotheses of Stacks 05YD itself, so that the three
theorems below display the hypotheses of the source; the three conclusions with nothing carried
are `Space.isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree`,
`AlgebraicGeometry.Space.hasProperty_isEtale_restrictionOfScalarsMap_of_isFiniteLocallyFree` and
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree`. Nothing
else is assumed.

## Main definitions

* `AlgebraicGeometry.Space.RestrictionPair.fibreBase`,
  `AlgebraicGeometry.Space.RestrictionPair.fibreBaseMap`,
  `AlgebraicGeometry.Space.RestrictionPair.fibreTotal` and
  `AlgebraicGeometry.Space.RestrictionPair.fibreTotalMap`: the data `W ⟶ Z_U ⟶ U` attached to a
  pair of Stacks 05Y9 over a scheme `U`.
* `AlgebraicGeometry.Space.RestrictionPair.fibreSections`: the restriction of scalars
  `Res_{Z_U/U}(W)` of that data, which is the functor of sections of Stacks 05XR.
* `AlgebraicGeometry.Space.RestrictionPair.ofFibrePair` and
  `AlgebraicGeometry.Space.RestrictionPair.toFibrePair`: the two directions of the
  identification of a section with a lifted pair.
* `AlgebraicGeometry.Space.restrictionOfScalarsFibreMap`: the induced morphism
  `Res_{Z_U/U}(W) ⟶ Res_{Z/Q}(X')`.
* `AlgebraicGeometry.Space.fibreComparison` and `AlgebraicGeometry.Space.fibreIso`: the
  comparison morphism to the fibre product and the isomorphism it is.
* `AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale` and
  `AlgebraicGeometry.Space.IsFibreSectionsSurjective`: the results of Stacks 05XR and 05XQ that
  are carried as hypotheses here; both are theorems, proved downstream of this file.
* `CategoryTheory.Limits.pullbackBaseChangeIso`: the identification of `T ×_U (U ×_Q Z)` with
  `T ×_Q Z`.

## Main results

* `AlgebraicGeometry.Space.isIso_fibreComparison`: the fibre of
  `Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` at a scheme-valued point is `Res_{Z_U/U}(W)`.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap`:
  **Stacks 05YD**, representability by algebraic spaces.
* `AlgebraicGeometry.Space.hasProperty_isEtale_restrictionOfScalarsMap`: **Stacks 05YD**,
  étaleness.
* `AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap`: **Stacks 05YD**, surjectivity
  when `X' ⟶ X` is surjective.

## Implementation notes

Étaleness of a morphism representable by algebraic spaces is
`AlgebraicGeometry.Space.HasProperty`, Stacks 03XZ: the property holds for every base change of
the morphism along a scheme-valued point of its target. Representability is
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces`, Stacks 02YQ, in the value universe
`u` of the site; the `ULift` variant is not needed, since all four presheaves here take values
in `Type u`. Surjectivity is Stacks 03ME, `AlgebraicGeometry.Space.IsSurjective`, the surjectivity
of the induced map on the point sets of Stacks 03BU.

The second component of a pair of Stacks 05Y9 lives over its first component, so comparisons of
pairs need a transport; it is isolated in
`AlgebraicGeometry.Space.RestrictionPair.lift_eq_of_eq`, which is the converse of the library's
`AlgebraicGeometry.Space.RestrictionPair.ext_of_base_eq`. For the same reason the two
constructions `ofFibrePair` and `toFibrePair` are reducible: their first components are
composites, and a goal about the fibre products they index is type-correct only once those have
been unfolded.

Every comparison of fibre products used below is stated as an abstract lemma about a general
category in the `CategoryTheory.Limits` section, so that the large presheaves of the application
appear only as arguments.

## References

* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace CategoryTheory.Limits

variable {C : Type w} [Category.{v} C] [HasPullbacks C]

/-- The comparison of two fibre products along a pair of equalities of their defining morphisms
is the identity when both equalities are reflexivity. -/
theorem pullback.congrHom_rfl {Xc Yc Zc : C} (f : Xc ⟶ Zc) (g : Yc ⟶ Zc) :
    (pullback.congrHom (rfl : f = f) (rfl : g = g)).hom = 𝟙 (pullback f g) :=
  pullback.hom_ext (by simp) (by simp)

variable {T T' U Qc Zc : C}

/-- **The fibre product `T ×_U (U ×_Q Z)` is the fibre product `T ×_{c ≫ a, Q} Z`.** One
pasting of cartesian squares: the first factor is a base change of `z` along `a`, so a morphism
to it over `T` is a morphism to `Z` over `Q`. -/
noncomputable def pullbackBaseChangeIso (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    pullback c (pullback.fst a z) ≅ pullback (c ≫ a) z :=
  (isPullback_fst_snd_comp_of_isPullback (IsPullback.of_hasPullback a z) c rfl).isoPullback

/-- The identification of `AlgebraicGeometry.Space.pullbackBaseChangeIso` is the identity on the
projection to `T`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_hom_fst (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    (pullbackBaseChangeIso a z c).hom ≫ pullback.fst (c ≫ a) z =
      pullback.fst c (pullback.fst a z) :=
  IsPullback.isoPullback_hom_fst _

/-- The identification of `CategoryTheory.Limits.pullbackBaseChangeIso` carries the projection to
`Z` to the composite of the two projections. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_hom_snd (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    (pullbackBaseChangeIso a z c).hom ≫ pullback.snd (c ≫ a) z =
      pullback.snd c (pullback.fst a z) ≫ pullback.snd a z :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `CategoryTheory.Limits.pullbackBaseChangeIso` on the projection to `T`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_inv_fst (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    (pullbackBaseChangeIso a z c).inv ≫ pullback.fst c (pullback.fst a z) =
      pullback.fst (c ≫ a) z :=
  IsPullback.isoPullback_inv_fst _

/-- The inverse of `CategoryTheory.Limits.pullbackBaseChangeIso` on the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_inv_snd (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    (pullbackBaseChangeIso a z c).inv ≫
        (pullback.snd c (pullback.fst a z) ≫ pullback.snd a z) =
      pullback.snd (c ≫ a) z :=
  IsPullback.isoPullback_inv_snd _

/-- **The projection `T ×_U (U ×_Q Z) ⟶ U ×_Q Z` is the base change of `c`**, read through
`CategoryTheory.Limits.pullbackBaseChangeIso`. -/
theorem snd_eq_pullbackBaseChangeIso_hom_map (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) :
    pullback.snd c (pullback.fst a z) =
      (pullbackBaseChangeIso a z c).hom ≫
        pullback.map (c ≫ a) z a z c (𝟙 Zc) (𝟙 Qc) (by simp) (by simp) := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.map_fst, pullbackBaseChangeIso_hom_fst_assoc]
    exact pullback.condition.symm
  · simp only [Category.assoc, pullback.map_snd, Category.comp_id,
      pullbackBaseChangeIso_hom_snd]

/-- **The identification of `CategoryTheory.Limits.pullbackBaseChangeIso` is natural in `T`.**
Any comparison `c₀` of the two fibre products over `U` and any comparison `m` of the two fibre
products over `Q` agree under the identification. -/
theorem pullbackBaseChangeIso_inv_naturality (a : U ⟶ Qc) (z : Zc ⟶ Qc) (c : T ⟶ U) (c' : T' ⟶ U)
    (φ : T' ⟶ T)
    (c₀ : pullback c' (pullback.fst a z) ⟶ pullback c (pullback.fst a z))
    (h₁ : c₀ ≫ pullback.fst c (pullback.fst a z) = pullback.fst c' (pullback.fst a z) ≫ φ)
    (h₂ : c₀ ≫ pullback.snd c (pullback.fst a z) = pullback.snd c' (pullback.fst a z))
    (m : pullback (c' ≫ a) z ⟶ pullback (c ≫ a) z)
    (hm₁ : m ≫ pullback.fst (c ≫ a) z = pullback.fst (c' ≫ a) z ≫ φ)
    (hm₂ : m ≫ pullback.snd (c ≫ a) z = pullback.snd (c' ≫ a) z) :
    (pullbackBaseChangeIso a z c').inv ≫ c₀ = m ≫ (pullbackBaseChangeIso a z c).inv := by
  have key : (pullbackBaseChangeIso a z c').hom ≫ m = c₀ ≫ (pullbackBaseChangeIso a z c).hom := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hm₁, pullbackBaseChangeIso_hom_fst_assoc,
        pullbackBaseChangeIso_hom_fst, h₁]
    · simp only [Category.assoc, hm₂, pullbackBaseChangeIso_hom_snd,
        ]
      rw [← Category.assoc, h₂]
  rw [Iso.inv_comp_eq, ← Category.assoc, key]
  simp

/-- The comparison of two fibre products at reflexivity is the identity, read on the inverse. -/
theorem pullback.congrHom_rfl_inv {Xc Yc Zc : C} (f : Xc ⟶ Zc) (g : Yc ⟶ Zc) :
    (pullback.congrHom (rfl : f = f) (rfl : g = g)).inv = 𝟙 (pullback f g) := by
  simp

/-- The inverse comparison of two fibre products along an equality of first components, on the
first projection. -/
theorem pullback.congrHom_inv_fst {Xc Yc Zc : C} {f₁ f₂ : Xc ⟶ Zc} (h : f₁ = f₂)
    (g : Yc ⟶ Zc) :
    (pullback.congrHom h (rfl : g = g)).inv ≫ pullback.fst f₁ g = pullback.fst f₂ g := by
  simp

/-- The inverse comparison of two fibre products along an equality of first components, on the
second projection. -/
theorem pullback.congrHom_inv_snd {Xc Yc Zc : C} {f₁ f₂ : Xc ⟶ Zc} (h : f₁ = f₂)
    (g : Yc ⟶ Zc) :
    (pullback.congrHom h (rfl : g = g)).inv ≫ pullback.snd f₁ g = pullback.snd f₂ g := by
  simp

/-- **An element of a fibre product of presheaves of types is determined by its two
projections.** -/
theorem pullbackObj_ext {C : Type w} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type v} (f : F ⟶ H)
    (g : G ⟶ H) {T : C} (y₁ y₂ : (pullback f g).obj (Opposite.op T))
    (h₁ : (pullback.fst f g).app (Opposite.op T) y₁ =
      (pullback.fst f g).app (Opposite.op T) y₂)
    (h₂ : (pullback.snd f g).app (Opposite.op T) y₁ =
      (pullback.snd f g).app (Opposite.op T) y₂) : y₁ = y₂ := by
  have key : (yonedaEquiv.symm y₁ : yoneda.obj T ⟶ pullback f g) = yonedaEquiv.symm y₂ := by
    refine pullback.hom_ext ?_ ?_
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₁]
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₂]
  exact yonedaEquiv.symm.injective key

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The second components of two equal pairs agree**, after the canonical identification of
the two fibre products their first components define. This is the converse of
`AlgebraicGeometry.Space.RestrictionPair.ext_of_base_eq`. -/
theorem RestrictionPair.lift_eq_of_eq {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p q : RestrictionPair B S hS x z T} (h : p = q) :
    p.lift = (pullback.congrHom (congrArg RestrictionPair.base h) rfl).hom ≫ q.lift := by
  subst h
  rw [pullback.congrHom_rfl, Category.id_comp]

/-- **The pair at a scheme-valued point of a restriction of scalars, restricted along a morphism
of the site.** -/
theorem RestrictionOfScalarsConstruction.pairEquiv_app {X Z Q : AlgebraicSpaces B S hS}
    {x : X ⟶ Z} {z : Z ⟶ Q} (R : RestrictionOfScalarsConstruction B S hS x z)
    {U T : BigFppfOver B S hS} (ξ : yoneda.obj U ⟶ R.presheaf) (s : T ⟶ U) :
    R.pairEquiv T (ξ.app (op T) s) =
      RestrictionPair.restrict (yoneda.map s) (R.pairEquiv U (yonedaEquiv ξ)) := by
  have h : ξ.app (op T) s = R.presheaf.map s.op (yonedaEquiv ξ) := by
    conv_lhs => rw [← Equiv.symm_apply_apply yonedaEquiv ξ]
    exact yonedaEquiv_symm_app_apply (yonedaEquiv ξ) (op T) s
  rw [h]
  exact RestrictionPair.eq_restrict_of_isPullbackAlong (R.natural s (yonedaEquiv ξ))

section Fibre

variable {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z} {x : X ⟶ Z} {z : Z ⟶ Q}
  {U : BigFppfOver B S hS}

/-- The base change `Z_U = U ×_{a, Q} Z` of `z : Z ⟶ Q` along the first component `a` of a pair
of Stacks 05Y9 over a scheme `U`. -/
noncomputable abbrev RestrictionPair.fibreBase
    (p : RestrictionPair B S hS x z (yoneda.obj U)) : AlgebraicSpaces B S hS :=
  ⟨pullback p.base z.hom,
    isAlgebraicSpace_pullback B S hS p.base z.hom (isAlgebraicSpace_yoneda B S hS U)
      Z.property Q.property⟩

/-- The structure morphism `Z_U ⟶ U` of `AlgebraicGeometry.Space.RestrictionPair.fibreBase`. -/
noncomputable abbrev RestrictionPair.fibreBaseMap
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    p.fibreBase ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.fst p.base z.hom)

/-- The fibre `W = Z_U ×_{b, X} X'` of `g : X' ⟶ X` over the second component `b` of a pair of
Stacks 05Y9 over a scheme `U`. -/
noncomputable abbrev RestrictionPair.fibreTotal (g : X' ⟶ X)
    (p : RestrictionPair B S hS x z (yoneda.obj U)) : AlgebraicSpaces B S hS :=
  ⟨pullback p.lift g.hom,
    isAlgebraicSpace_pullback B S hS p.lift g.hom p.fibreBase.property X'.property X.property⟩

/-- The morphism `W ⟶ Z_U` of `AlgebraicGeometry.Space.RestrictionPair.fibreTotal`. -/
noncomputable abbrev RestrictionPair.fibreTotalMap (g : X' ⟶ X)
    (p : RestrictionPair B S hS x z (yoneda.obj U)) : p.fibreTotal g ⟶ p.fibreBase :=
  ObjectProperty.homMk (pullback.fst p.lift g.hom)

/-- The restriction of scalars `Res_{Z_U/U}(W)` of the fibre data of a pair: the functor of
sections of `W ⟶ Z_U` over `U` studied in Stacks 05XR. -/
noncomputable abbrev RestrictionPair.fibreSections (g : X' ⟶ X)
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    RestrictionOfScalarsConstruction B S hS (p.fibreTotalMap g) p.fibreBaseMap :=
  restrictionOfScalars B S hS (p.fibreTotalMap g) p.fibreBaseMap

/-- **A section of `W_T → Z_T` is a pair of `Res_{Z/Q}(X')` lying over the given pair of
`Res_{Z/Q}(X)`.** The first component is the composite `T ⟶ U ⟶ Q`, and the second is the
projection of the section to `X'`, read through the identification of `T ×_U Z_U` with
`T ×_Q Z`. -/
noncomputable abbrev RestrictionPair.ofFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    RestrictionPair B S hS x' z T where
  base := q.base ≫ p.base
  lift := (pullbackBaseChangeIso p.base z.hom q.base).inv ≫ q.lift ≫ pullback.snd p.lift g.hom
  over := by
    have hx : g.hom ≫ x.hom = x'.hom := congrArg (fun k : X' ⟶ Z => k.hom) hg
    have h1 : q.lift ≫ pullback.fst p.lift g.hom =
        pullback.snd q.base (pullback.fst p.base z.hom) := q.over
    have h2 : q.lift ≫ pullback.snd p.lift g.hom ≫ x'.hom =
        pullback.snd q.base (pullback.fst p.base z.hom) ≫ pullback.snd p.base z.hom := by
      rw [← hx, ← Category.assoc (pullback.snd p.lift g.hom), ← pullback.condition,
        Category.assoc, ← Category.assoc q.lift, h1, p.over]
    rw [Category.assoc, Category.assoc, h2]
    exact pullbackBaseChangeIso_inv_snd p.base z.hom q.base

/-- The first component of `AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`. -/
@[simp]
theorem RestrictionPair.ofFibrePair_base (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    (p.ofFibrePair g hg q).base = q.base ≫ p.base := rfl

/-- The second component of `AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`. -/
@[simp]
theorem RestrictionPair.ofFibrePair_lift (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    (p.ofFibrePair g hg q).lift =
      (pullbackBaseChangeIso p.base z.hom q.base).inv ≫
        q.lift ≫ pullback.snd p.lift g.hom := rfl

/-- **`AlgebraicGeometry.Space.RestrictionPair.ofFibrePair` commutes with base change.** The
comparison of the two fibre products over `Q` is the base change of `f`, and it matches the
given comparison of the two fibre products over `U` under the identification of
`CategoryTheory.Limits.pullbackBaseChangeIso`. -/
theorem RestrictionPair.isPullbackAlong_ofFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T}
    {q' : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T'}
    (h : RestrictionPair.IsPullbackAlong f q q') :
    RestrictionPair.IsPullbackAlong f (p.ofFibrePair g hg q) (p.ofFibrePair g hg q') := by
  obtain ⟨hbase, c₀, hc₁, hc₂, hlift⟩ := h
  have hbase' : q'.base ≫ p.base = f ≫ q.base ≫ p.base := by
    rw [hbase, Category.assoc]
  have hm₀ : (q'.base ≫ p.base) ≫ 𝟙 Q.obj = f ≫ q.base ≫ p.base := by
    rw [Category.comp_id, hbase']
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback (q'.base ≫ p.base) z.hom ⟶ pullback (q.base ≫ p.base) z.hom,
      m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f ∧ m ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.map _ _ _ _ f (𝟙 Z.obj) (𝟙 Q.obj) hm₀ (by simp), pullback.map_fst _ _ _ _ _ _ _ _ _,
      by rw [pullback.map_snd, Category.comp_id]⟩
  refine ⟨hbase', ?_⟩
  simp only [RestrictionPair.ofFibrePair_base]
  refine ⟨m, hm₁, hm₂, ?_⟩
  have hnat := pullbackBaseChangeIso_inv_naturality p.base z.hom q.base q'.base f c₀ hc₁ hc₂
    m hm₁ hm₂
  rw [hlift]
  simp only [Category.assoc]
  rw [← Category.assoc (pullbackBaseChangeIso p.base z.hom q'.base).inv c₀, hnat]
  simp only [Category.assoc]

/-- **The pairs of `AlgebraicGeometry.Space.RestrictionPair.ofFibrePair` are compatible with the
restriction maps of `Res_{Z_U/U}(W)`.** -/
theorem restrictionOfScalarsFibrePair_natural (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    ∀ {T T' : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ T')
      (v : (p.fibreSections g).presheaf.obj T),
      p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T'.unop
          ((p.fibreSections g).presheaf.map f v)) =
        RestrictionPair.restrict (yoneda.map f.unop)
          (p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v)) :=
  fun f v => RestrictionPair.eq_restrict_of_isPullbackAlong
    (p.isPullbackAlong_ofFibrePair g hg ((p.fibreSections g).natural f.unop v))

/-- **The morphism `Res_{Z_U/U}(W) ⟶ Res_{Z/Q}(X')` of the fibre data of a pair.** A section of
`W_T → Z_T` over `T/U` is a pair of `Res_{Z/Q}(X')` over `T`, by
`AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`, compatibly with base change. -/
noncomputable def restrictionOfScalarsFibreMap (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    (p.fibreSections g).presheaf ⟶ (restrictionOfScalars B S hS x' z).presheaf :=
  restrictionOfScalarsOfPairs (restrictionOfScalars B S hS x' z)
    (fun T v => p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v))
    (restrictionOfScalarsFibrePair_natural g hg p)

/-- The pair of `Res_{Z/Q}(X')` that
`AlgebraicGeometry.Space.restrictionOfScalarsFibreMap` attaches to a section. -/
@[simp]
theorem pairEquiv_restrictionOfScalarsFibreMap (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) (T : (BigFppfOver B S hS)ᵒᵖ)
    (v : (p.fibreSections g).presheaf.obj T) :
    (restrictionOfScalars B S hS x' z).pairEquiv T.unop
        ((restrictionOfScalarsFibreMap g hg p).app T v) =
      p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T.unop v) :=
  pairEquiv_restrictionOfScalarsOfPairs _ _ (restrictionOfScalarsFibrePair_natural g hg p) _ _

/-- The scheme-valued point of `Res_{Z/Q}(X)` determined by a pair of Stacks 05Y9 over a scheme
`U`. -/
noncomputable abbrev RestrictionPair.point (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    yoneda.obj U ⟶ (restrictionOfScalars B S hS x z).presheaf :=
  yonedaEquiv.symm (((restrictionOfScalars B S hS x z).pairEquiv U).symm p)

/-- The pair of `AlgebraicGeometry.Space.RestrictionPair.point`. -/
@[simp]
theorem RestrictionPair.pairEquiv_point (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    (restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv p.point) = p := by
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Postcomposing the pair of a section of `Res_{Z_U/U}(W)` with `g` gives the base change of
the given pair.** This is the defining property of the fibre: a section of `W_T → Z_T` is a pair
of `Res_{Z/Q}(X')` lifting the restriction of `(a, b)` to `T`. -/
theorem RestrictionPair.postcomp_ofFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    RestrictionPair.postcomp g hg (p.ofFibrePair g hg q) = RestrictionPair.restrict q.base p := by
  have h1 : q.lift ≫ pullback.fst p.lift g.hom =
      pullback.snd q.base (pullback.fst p.base z.hom) := q.over
  set m := pullback.map (q.base ≫ p.base) z.hom p.base z.hom q.base (𝟙 Z.obj) (𝟙 Q.obj)
    (by simp) (by simp) with hm
  have key : ((pullbackBaseChangeIso p.base z.hom q.base).inv ≫
        q.lift ≫ pullback.snd p.lift g.hom) ≫ g.hom = m ≫ p.lift := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc q.lift, h1,
      snd_eq_pullbackBaseChangeIso_hom_map p.base z.hom q.base, Category.assoc,
      Iso.inv_hom_id_assoc]
  refine RestrictionPair.eq_restrict_of_isPullbackAlong (f := q.base)
    ⟨rfl, m, pullback.map_fst _ _ _ _ _ _ _ _ _,
      (pullback.map_snd _ _ _ _ _ _ _ _ _).trans (Category.comp_id _), key⟩

/-- **The square of the fibre data commutes.** The projection of `Res_{Z_U/U}(W)` to `U`
followed by the given point of `Res_{Z/Q}(X)` is
`AlgebraicGeometry.Space.restrictionOfScalarsFibreMap` followed by the restriction-of-scalars
map of `g`. -/
theorem restrictionOfScalarsFibreMap_comp (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    (p.fibreSections g).projection ≫ p.point =
      restrictionOfScalarsFibreMap g hg p ≫ (restrictionOfScalarsMap g hg z).1 := by
  ext T v
  refine ((restrictionOfScalars B S hS x z).pairEquiv T.unop).injective ?_
  show (restrictionOfScalars B S hS x z).pairEquiv T.unop
      (p.point.app T ((p.fibreSections g).projection.app T v)) =
    (restrictionOfScalars B S hS x z).pairEquiv T.unop
      ((restrictionOfScalarsMap g hg z).1.app T ((restrictionOfScalarsFibreMap g hg p).app T v))
  have hl : (restrictionOfScalars B S hS x z).pairEquiv T.unop
      (p.point.app T ((p.fibreSections g).projection.app T v)) =
        RestrictionPair.restrict ((p.fibreSections g).pairEquiv T.unop v).base p := by
    rw [(p.fibreSections g).projection_pairEquiv T.unop v,
      (restrictionOfScalars B S hS x z).pairEquiv_app p.point
        (yonedaEquiv ((p.fibreSections g).pairEquiv T.unop v).base),
      yoneda_map_yonedaEquiv, RestrictionPair.pairEquiv_point]
  rw [hl, (restrictionOfScalarsMap g hg z).2 T.unop
      ((restrictionOfScalarsFibreMap g hg p).app T v),
    pairEquiv_restrictionOfScalarsFibreMap, RestrictionPair.postcomp_ofFibrePair]

/-- **The first components of a lifted pair and of the base change agree.** -/
theorem RestrictionPair.base_eq_of_postcomp_eq (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    r.base = c ≫ p.base :=
  congrArg RestrictionPair.base h

/-- **The second components of a lifted pair and of the base change agree**, after the canonical
identification of the two fibre products. -/
theorem RestrictionPair.lift_comp_eq_of_postcomp_eq (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    r.lift ≫ g.hom =
      (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).hom ≫
        pullback.map (c ≫ p.base) z.hom p.base z.hom c (𝟙 Z.obj) (𝟙 Q.obj) (by simp) (by simp) ≫
          p.lift :=
  RestrictionPair.lift_eq_of_eq h

/-- **The two components of `AlgebraicGeometry.Space.RestrictionPair.toFibrePair` land in the
fibre product `W = Z_U ×_{b, X} X'`.** The second component of the lifted pair postcomposed with
`g` is the second component of the base change of `(a, b)`, which is the projection to `Z_U`
read through `CategoryTheory.Limits.pullbackBaseChangeIso`. -/
theorem RestrictionPair.toFibrePair_condition (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    pullback.snd c (pullback.fst p.base z.hom) ≫ p.lift =
      ((pullbackBaseChangeIso p.base z.hom c).hom ≫
        (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.lift) ≫ g.hom := by
  rw [Category.assoc, Category.assoc, p.lift_comp_eq_of_postcomp_eq g hg c r h,
    Iso.inv_hom_id_assoc, snd_eq_pullbackBaseChangeIso_hom_map p.base z.hom c, Category.assoc]

/-- **A pair of `Res_{Z/Q}(X')` lifting the base change of the given pair is a section of
`W_T → Z_T`.** This is the inverse of `AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`: the
section is the pair consisting of the projection to `Z_T` and the second component of the lifted
pair, which lands in `W = Z_U ×_{b, X} X'` by
`AlgebraicGeometry.Space.RestrictionPair.toFibrePair_condition`. -/
noncomputable abbrev RestrictionPair.toFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T where
  base := c
  lift :=
    pullback.lift (pullback.snd c (pullback.fst p.base z.hom))
      ((pullbackBaseChangeIso p.base z.hom c).hom ≫
        (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.lift)
      (p.toFibrePair_condition g hg c r h)
  over := pullback.lift_fst _ _ _

/-- The first component of `AlgebraicGeometry.Space.RestrictionPair.toFibrePair`. -/
@[simp]
theorem RestrictionPair.toFibrePair_base (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    (p.toFibrePair g hg c r h).base = c := rfl

/-- **`AlgebraicGeometry.Space.RestrictionPair.toFibrePair` is a section of
`AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`.** -/
theorem RestrictionPair.ofFibrePair_toFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ yoneda.obj U)
    (r : RestrictionPair B S hS x' z T)
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p) :
    r = p.ofFibrePair g hg (p.toFibrePair g hg c r h) := by
  refine RestrictionPair.ext_of_base_eq (p.base_eq_of_postcomp_eq g hg c r h) ?_
  show r.lift = (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).hom ≫
      (pullbackBaseChangeIso p.base z.hom c).inv ≫
        pullback.lift (pullback.snd c (pullback.fst p.base z.hom))
            ((pullbackBaseChangeIso p.base z.hom c).hom ≫
              (pullback.congrHom (p.base_eq_of_postcomp_eq g hg c r h) rfl).inv ≫ r.lift)
            (p.toFibrePair_condition g hg c r h) ≫
          pullback.snd p.lift g.hom
  rw [pullback.lift_snd, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **`AlgebraicGeometry.Space.RestrictionPair.toFibrePair` inverts
`AlgebraicGeometry.Space.RestrictionPair.ofFibrePair`.** -/
theorem RestrictionPair.toFibrePair_ofFibrePair (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : RestrictionPair B S hS (p.fibreTotalMap g) p.fibreBaseMap T) :
    p.toFibrePair g hg q.base (p.ofFibrePair g hg q)
        (p.postcomp_ofFibrePair g hg q) = q := by
  have hb := p.base_eq_of_postcomp_eq g hg q.base (p.ofFibrePair g hg q)
    (p.postcomp_ofFibrePair g hg q)
  have hlift : (p.toFibrePair g hg q.base (p.ofFibrePair g hg q)
      (p.postcomp_ofFibrePair g hg q)).lift = q.lift := by
    refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans q.over.symm) ?_
    rw [pullback.lift_snd, RestrictionPair.ofFibrePair_lift, pullback.congrHom_rfl_inv,
      Category.id_comp, Iso.hom_inv_id_assoc]
  exact RestrictionPair.ext_of_base_eq rfl
    (hlift.trans (by rw [pullback.congrHom_rfl, Category.id_comp]))

/-- **The comparison morphism from `Res_{Z_U/U}(W)` to the fibre product of `Res_{Z/Q}(X')` and
`U` over `Res_{Z/Q}(X)`.** -/
noncomputable def fibreComparison (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    (p.fibreSections g).presheaf ⟶ pullback p.point (restrictionOfScalarsMap g hg z).1 :=
  pullback.lift (p.fibreSections g).projection (restrictionOfScalarsFibreMap g hg p)
    (restrictionOfScalarsFibreMap_comp g hg p)

/-- The comparison morphism followed by the projection to `U`. -/
@[reassoc (attr := simp)]
theorem fibreComparison_fst (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    fibreComparison g hg p ≫ pullback.fst p.point (restrictionOfScalarsMap g hg z).1 =
      (p.fibreSections g).projection :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the projection to `Res_{Z/Q}(X')`. -/
@[reassoc (attr := simp)]
theorem fibreComparison_snd (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    fibreComparison g hg p ≫ pullback.snd p.point (restrictionOfScalarsMap g hg z).1 =
      restrictionOfScalarsFibreMap g hg p :=
  pullback.lift_snd _ _ _

/-- **`AlgebraicGeometry.Space.RestrictionPair.toFibrePair` depends only on its data.** -/
theorem RestrictionPair.toFibrePair_congr (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U))
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c c' : T ⟶ yoneda.obj U}
    {r r' : RestrictionPair B S hS x' z T}
    (h : RestrictionPair.postcomp g hg r = RestrictionPair.restrict c p)
    (h' : RestrictionPair.postcomp g hg r' = RestrictionPair.restrict c' p)
    (hc : c = c') (hr : r = r') :
    p.toFibrePair g hg c r h = p.toFibrePair g hg c' r' h' := by
  subst hc
  subst hr
  rfl

/-- **The comparison morphism is an isomorphism**: a section of `Res_{Z_U/U}(W)` over `T` is the
same thing as a morphism `T ⟶ U` together with a pair of `Res_{Z/Q}(X')` over `T` lifting the
base change of `(a, b)`. This is the identification of the fibre of
`Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` at a scheme-valued point with the functor of sections of
Stacks 05XR. -/
instance isIso_fibreComparison (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) : IsIso (fibreComparison g hg p) := by
  have happ : ∀ T, IsIso ((fibreComparison g hg p).app T) := by
    intro T
    obtain ⟨T⟩ := T
    have hfst : ∀ v, (pullback.fst p.point (restrictionOfScalarsMap g hg z).1).app (op T)
        ((fibreComparison g hg p).app (op T) v) =
          (p.fibreSections g).projection.app (op T) v :=
      fun v => congrArg (fun k => (k.app (op T)) v) (fibreComparison_fst g hg p)
    have hsnd : ∀ v, (pullback.snd p.point (restrictionOfScalarsMap g hg z).1).app (op T)
        ((fibreComparison g hg p).app (op T) v) =
          (restrictionOfScalarsFibreMap g hg p).app (op T) v :=
      fun v => congrArg (fun k => (k.app (op T)) v) (fibreComparison_snd g hg p)
    rw [isIso_iff_bijective]
    refine ⟨fun v₁ v₂ hv => ?_, fun y => ?_⟩
    · refine ((p.fibreSections g).pairEquiv T).injective ?_
      have hb : ((p.fibreSections g).pairEquiv T v₁).base =
          ((p.fibreSections g).pairEquiv T v₂).base := by
        refine yonedaEquiv.injective ?_
        rw [← (p.fibreSections g).projection_pairEquiv T v₁,
          ← (p.fibreSections g).projection_pairEquiv T v₂, ← hfst v₁, ← hfst v₂, hv]
      have hr : p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T v₁) =
          p.ofFibrePair g hg ((p.fibreSections g).pairEquiv T v₂) := by
        rw [← pairEquiv_restrictionOfScalarsFibreMap g hg p (op T) v₁,
          ← pairEquiv_restrictionOfScalarsFibreMap g hg p (op T) v₂, ← hsnd v₁, ← hsnd v₂, hv]
      refine ((RestrictionPair.toFibrePair_ofFibrePair g hg p
          ((p.fibreSections g).pairEquiv T v₁)).symm.trans ?_)
      exact (RestrictionPair.toFibrePair_congr g hg p _ _ hb hr).trans
        (RestrictionPair.toFibrePair_ofFibrePair g hg p ((p.fibreSections g).pairEquiv T v₂))
    · have hc : p.point.app (op T)
            ((pullback.fst p.point (restrictionOfScalarsMap g hg z).1).app (op T) y) =
          (restrictionOfScalarsMap g hg z).1.app (op T)
            ((pullback.snd p.point (restrictionOfScalarsMap g hg z).1).app (op T) y) :=
        congrArg (fun k => (k.app (op T)) y) (pullback.condition (f := p.point)
          (g := (restrictionOfScalarsMap g hg z).1))
      have hpair : RestrictionPair.postcomp g hg
          ((restrictionOfScalars B S hS x' z).pairEquiv T
            ((pullback.snd p.point (restrictionOfScalarsMap g hg z).1).app (op T) y)) =
          RestrictionPair.restrict
            (yoneda.map ((pullback.fst p.point (restrictionOfScalarsMap g hg z).1).app (op T) y))
            p := by
        rw [← (restrictionOfScalarsMap g hg z).2 T _, ← hc,
          (restrictionOfScalars B S hS x z).pairEquiv_app p.point _,
          RestrictionPair.pairEquiv_point]
      refine ⟨((p.fibreSections g).pairEquiv T).symm (p.toFibrePair g hg _ _ hpair), ?_⟩
      refine pullbackObj_ext p.point (restrictionOfScalarsMap g hg z).1 _ y ?_ ?_
      · rw [hfst, (p.fibreSections g).projection_pairEquiv, Equiv.apply_symm_apply,
          RestrictionPair.toFibrePair_base, yonedaEquiv_yoneda_map]
      · rw [hsnd]
        refine ((restrictionOfScalars B S hS x' z).pairEquiv T).injective ?_
        rw [pairEquiv_restrictionOfScalarsFibreMap, Equiv.apply_symm_apply]
        exact (RestrictionPair.ofFibrePair_toFibrePair g hg p _ _ hpair).symm
  exact NatIso.isIso_of_isIso_app _

/-- **The fibre of `Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` at a scheme-valued point is `Res_{Z_U/U}(W)`,**
the functor of sections of `W ⟶ Z_U` over `U` of Stacks 05XR. -/
noncomputable def fibreIso (g : X' ⟶ X) (hg : g ≫ x = x')
    (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    (p.fibreSections g).presheaf ≅ pullback p.point (restrictionOfScalarsMap g hg z).1 :=
  asIso (fibreComparison g hg p)

end Fibre

/-! ### Stacks 05YD -/

/-- **The input from Stacks 05XR**, in the form in which the proof of Stacks 05YD uses it: for
every scheme `U` of the site, every algebraic space `Z_U` exhibited as the base change
`U ×_{a, Q} Z` of `z` and every algebraic space `W` exhibited as the fibre product
`Z_U ×_{b, X} X'` of `g`, the restriction of scalars `Res_{Z_U/U}(W)` — which is the functor
`U' ↦ {σ : (Z_U)_{U'} → W_{U'} a section}` of Stacks 05XR — is an algebraic space étale over
`U`.

The assertion is premised on the two hypotheses of Stacks 05YD, that `g` is étale and that `z`
is finite locally free: those are exactly what Stacks 05XR needs, after transporting them along
base change to `W ⟶ Z_U` and `Z_U ⟶ U`.

This abbreviation is **no longer an open assumption**: it is the theorem
`AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`. That theorem assembles the general case
of Stacks 05XR — `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isEtale` and
`AlgebraicGeometry.Space.isEtale_sectionSpace_of_isEtale`, with no separatedness — with the
bridge from a space of sections to a restriction of scalars,
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_relocalize` and
`AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars_relocalize`, after recognizing
arbitrary fibre data as relocalized data. The two recognitions are: `Z_U` is represented by an
object of the site over `U`, because `z` is affine — the first conjunct of Stacks 03ZV — and
affineness gives relative representability by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`, with the represented base
change finite as a morphism of schemes by Stacks 03ZU, through
`AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree`; and `W` is the lower-shriek
relocalization of the fibre of its own structural morphism over the tautological section, which
is `AlgebraicGeometry.Space.relocalizeToYoneda_fibreOfSection_eq`.

It survives as a named hypothesis only because the theorems below sit upstream of that proof in
the import graph: the finiteness input from Stacks 03ZU lives in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartComparisonAssembly.lean`, which already imports this
file. The first two conclusions of Stacks 05YD with nothing carried are
`Space.isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree` and
`AlgebraicGeometry.Space.hasProperty_isEtale_restrictionOfScalarsMap_of_isFiniteLocallyFree`.

The stability of "étale" under base change is *not* among what is carried: it is
`AlgebraicGeometry.Space.isEtale_of_isPullback`, Stacks 03FU. -/
abbrev IsFibreSectionsAlgebraicEtale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Z Q : AlgebraicSpaces B S hS} (g : X' ⟶ X) (z : Z ⟶ Q) : Prop :=
  IsEtale B S hS g.hom → IsFiniteLocallyFree B S hS z →
    ∀ (U : BigFppfOver B S hS) (ZU W : AlgebraicSpaces B S hS)
      (ζ : ZU ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
      (w : W ⟶ ZU) (a : yoneda.obj U ⟶ Q.obj) (ι : ZU.obj ⟶ Z.obj) (b : ZU.obj ⟶ X.obj)
      (κ : W.obj ⟶ X'.obj),
      IsPullback ζ.hom ι a z.hom → IsPullback w.hom κ b g.hom →
        IsAlgebraicSpace B S hS (restrictionOfScalars B S hS w ζ).presheaf ∧
          IsEtale B S hS (restrictionOfScalars B S hS w ζ).projection

/-- **The input from Stacks 05XQ**, in the form in which the proof of Stacks 05YD uses it: in the
situation of `AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`, the morphism
`Res_{Z_U/U}(W) ⟶ U` is surjective. This is what Stacks 05XQ supplies — a section of
`W_{U'} → (Z_U)_{U'}` after a surjective étale base change `U' → U`, which is proved as
`AlgebraicGeometry.Space.exists_surjective_etale_sectionsOver`.

This abbreviation is **no longer an open assumption**: the passage from that form to surjectivity
of `Res_{Z_U/U}(W) ⟶ U` is the theorem `AlgebraicGeometry.Space.isFibreSectionsSurjective`, which
transports 05XQ across the identification of `Z_U` with the represented base change,
scheme-level finiteness coming from `AlgebraicGeometry.Space.presheaf_of_isFiniteLocallyFree`.
It survives as a named hypothesis only because the theorems below sit upstream of that proof in
the import graph; the conclusions of Stacks 05YD and 05Y5 with nothing carried are
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree` and
`AlgebraicGeometry.Space.isSurjective_relativeHomPostcompose_of_isFiniteLocallyFree`.

The assertion is premised on the hypotheses of the last sentence of Stacks 05YD: `g` is étale and
surjective and `z` is finite locally free. -/
abbrev IsFibreSectionsSurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Z Q : AlgebraicSpaces B S hS} (g : X' ⟶ X) (z : Z ⟶ Q) : Prop :=
  IsEtale B S hS g.hom → IsSurjective B S hS g.hom → IsFiniteLocallyFree B S hS z →
    ∀ (U : BigFppfOver B S hS) (ZU W : AlgebraicSpaces B S hS)
      (ζ : ZU ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
      (w : W ⟶ ZU) (a : yoneda.obj U ⟶ Q.obj) (ι : ZU.obj ⟶ Z.obj) (b : ZU.obj ⟶ X.obj)
      (κ : W.obj ⟶ X'.obj),
      IsPullback ζ.hom ι a z.hom → IsPullback w.hom κ b g.hom →
        IsSurjective B S hS (restrictionOfScalars B S hS w ζ).projection

/-- Étaleness of a morphism of presheaves on the big fppf site of `S` is unchanged by
precomposition with an isomorphism. -/
theorem IsEtale.of_iso_comp {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ F')
    {f : F' ⟶ G} (h : IsEtale B S hS (e.hom ≫ f)) : IsEtale B S hS f := by
  intro V φ hφ
  have h2 := h V (φ ≫ e.inv) (MorphismProperty.RespectsIso.postcomp _ e.inv φ hφ)
  simpa using h2

section Main

variable {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z} {x : X ⟶ Z}
  (g : X' ⟶ X) (hg : g ≫ x = x') (z : Z ⟶ Q)

/-- The pair of a scheme-valued point of `Res_{Z/Q}(X)` determines the point. -/
theorem point_pairEquiv {U : BigFppfOver B S hS}
    (ξ : yoneda.obj U ⟶ (restrictionOfScalars B S hS x z).presheaf) :
    ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ)).point = ξ := by
  rw [RestrictionPair.point, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The fibre data of a pair over a scheme instantiates
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`: `Z_U` is the base change of `z` along
the first component and `W` is the fibre product of `g` over the second. -/
theorem fibreSections_algebraic_etale (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z)
    (hg_etale : IsEtale B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    {U : BigFppfOver B S hS} (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    IsAlgebraicSpace B S hS (p.fibreSections g).presheaf ∧
      IsEtale B S hS (p.fibreSections g).projection :=
  h05XR hg_etale hz U p.fibreBase (p.fibreTotal g) p.fibreBaseMap
    (p.fibreTotalMap g) p.base (pullback.snd p.base z.hom) p.lift (pullback.snd p.lift g.hom)
    (IsPullback.of_hasPullback p.base z.hom) (IsPullback.of_hasPullback p.lift g.hom)

/-- The fibre data of a pair over a scheme instantiates
`AlgebraicGeometry.Space.IsFibreSectionsSurjective`. -/
theorem fibreSections_surjective (h05XQ : IsFibreSectionsSurjective B S hS g z)
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z)
    {U : BigFppfOver B S hS} (p : RestrictionPair B S hS x z (yoneda.obj U)) :
    IsSurjective B S hS (p.fibreSections g).projection :=
  h05XQ hg_etale hg_surjective hz U p.fibreBase (p.fibreTotal g) p.fibreBaseMap
    (p.fibreTotalMap g) p.base (pullback.snd p.base z.hom) p.lift (pullback.snd p.lift g.hom)
    (IsPullback.of_hasPullback p.base z.hom) (IsPullback.of_hasPullback p.lift g.hom)

/-- **Stacks 05YD, first conclusion.** Let `X' → X → Z → B` be morphisms of algebraic spaces over
a scheme `S`, with `X' → X` étale and `Z → B` finite locally free. Then
`Res_{Z/B}(X') → Res_{Z/B}(X)` is representable by algebraic spaces.

The hypotheses on `g` and `z` enter through
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`, which is the assertion of Stacks 05XR
for the fibre data `W ⟶ Z_U ⟶ U` the proof produces; see its docstring.

This is the general form, which takes that input as a hypothesis, and it carries no Stacks tag.
Stacks 05YD is registered on
`Space.isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree`, which
proves the same conclusion at the hypotheses of the source, with nothing carried. -/
theorem isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap
    (hg_etale : IsEtale B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z) :
    IsRepresentableByAlgebraicSpaces B S hS (restrictionOfScalarsMap g hg z).1 := by
  intro U ξ
  rw [← point_pairEquiv z ξ]
  exact (fibreSections_algebraic_etale g z h05XR hg_etale hz
      ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ))).1.of_iso
    (fibreIso g hg ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ)))

/-- **Stacks 05YD, second conclusion.** In the situation of
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap`, the morphism
`Res_{Z/B}(X') → Res_{Z/B}(X)` is étale: every base change of it along a scheme-valued point of
its target is an étale morphism of algebraic spaces.

This is the general form, which takes that input as a hypothesis, and it carries no Stacks tag.
Stacks 05YD is registered on
`AlgebraicGeometry.Space.hasProperty_isEtale_restrictionOfScalarsMap_of_isFiniteLocallyFree`,
which proves the same conclusion at the hypotheses of the source, with nothing carried. -/
theorem hasProperty_isEtale_restrictionOfScalarsMap
    (hg_etale : IsEtale B S hS g.hom) (hz : IsFiniteLocallyFree B S hS z)
    (h05XR : IsFibreSectionsAlgebraicEtale B S hS g z) :
    HasProperty B S hS (fun _ _ f => IsEtale B S hS f.hom) (restrictionOfScalarsMap g hg z).1
      (isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap g hg z hg_etale hz h05XR) := by
  intro U ξ
  have he := (fibreSections_algebraic_etale g z h05XR hg_etale hz
    ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ))).2
  have hp : ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ)).point = ξ :=
    point_pairEquiv z ξ
  show IsEtale B S hS (pullback.fst ξ (restrictionOfScalarsMap g hg z).1)
  rw [← hp]
  refine IsEtale.of_iso_comp
    (fibreIso g hg ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ))) ?_
  rw [fibreIso, asIso_hom, fibreComparison_fst]
  exact he

/-- **Stacks 05YD, third conclusion.** If `X' → X` is in addition surjective then
`Res_{Z/B}(X') → Res_{Z/B}(X)` is surjective.

Surjectivity of `g` enters through `AlgebraicGeometry.Space.IsFibreSectionsSurjective`, which is
the assertion Stacks 05XQ supplies for the fibre data `W ⟶ Z_U ⟶ U`; see its docstring. The
proof is the commuting square of the fibre data: a field-valued point of `Res_{Z/B}(X)` is a
scheme-valued point `ξ` of it, the fibre of the restriction-of-scalars map at `ξ` has a point
over the tautological point of `U`, and its image in `Res_{Z/B}(X')` is the required lift.

This is the general form, which takes that input as a hypothesis, and it carries no Stacks tag.
Stacks 05YD is registered on
`AlgebraicGeometry.Space.isSurjective_restrictionOfScalarsMap_of_isFiniteLocallyFree`,
which proves the same conclusion at the hypotheses of the source, with nothing carried. -/
theorem isSurjective_restrictionOfScalarsMap
    (hg_etale : IsEtale B S hS g.hom) (hg_surjective : IsSurjective B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z)
    (h05XQ : IsFibreSectionsSurjective B S hS g z) :
    IsSurjective B S hS (restrictionOfScalarsMap g hg z).1 := by
  intro P
  induction P using Quot.ind with
  | _ p₀ =>
    set U := p₀.siteObject with hU
    set ξ : yoneda.obj U ⟶ (restrictionOfScalars B S hS x z).presheaf :=
      yonedaEquiv.symm p₀.value with hξ
    set p := (restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ξ) with hpdef
    have hp : p.point = ξ := point_pairEquiv z ξ
    have hsp := fibreSections_surjective g z h05XQ hg_etale hg_surjective hz p
    let e : FieldValuedPoint B S hS (yoneda.obj U) :=
      { carrier := p₀.carrier
        field := p₀.field
        contained := p₀.contained
        toBase := p₀.toBase
        value := 𝟙 U }
    obtain ⟨ρ, hρ⟩ := hsp (e.class B S hS (yoneda.obj U))
    refine ⟨pointsMap B S hS (p.fibreSections g).presheaf
      (restrictionOfScalarsFibreMap g hg p) ρ, ?_⟩
    have hval : ξ.app (op U) (𝟙 U) = p₀.value := Equiv.apply_symm_apply yonedaEquiv p₀.value
    have hcls : (FieldValuedPoint.map B S hS (yoneda.obj U) ξ e).class B S hS
        (restrictionOfScalars B S hS x z).presheaf =
          p₀.class B S hS (restrictionOfScalars B S hS x z).presheaf := by
      refine Quot.sound ⟨p₀, ⟨𝟙 U, ?_⟩,
        FieldValuedPoint.dominates_refl B S hS
          (restrictionOfScalars B S hS x z).presheaf p₀⟩
      show (restrictionOfScalars B S hS x z).presheaf.map (𝟙 (op U))
        ((FieldValuedPoint.map B S hS (yoneda.obj U) ξ e).value) = p₀.value
      rw [CategoryTheory.Functor.map_id]
      exact hval
    calc pointsMap B S hS (restrictionOfScalars B S hS x' z).presheaf
            (restrictionOfScalarsMap g hg z).1
            (pointsMap B S hS (p.fibreSections g).presheaf
              (restrictionOfScalarsFibreMap g hg p) ρ)
        = pointsMap B S hS (p.fibreSections g).presheaf
            (restrictionOfScalarsFibreMap g hg p ≫ (restrictionOfScalarsMap g hg z).1) ρ :=
          (congrFun (pointsMap_comp B S hS (p.fibreSections g).presheaf
            (restrictionOfScalarsFibreMap g hg p) (restrictionOfScalarsMap g hg z).1) ρ).symm
      _ = pointsMap B S hS (p.fibreSections g).presheaf
            ((p.fibreSections g).projection ≫ p.point) ρ := by
          rw [restrictionOfScalarsFibreMap_comp g hg p]
      _ = pointsMap B S hS (yoneda.obj U) p.point
            (pointsMap B S hS (p.fibreSections g).presheaf
              (p.fibreSections g).projection ρ) :=
          congrFun (pointsMap_comp B S hS (p.fibreSections g).presheaf
            (p.fibreSections g).projection p.point) ρ
      _ = pointsMap B S hS (yoneda.obj U) ξ (e.class B S hS (yoneda.obj U)) := by
          rw [hρ, hp]
      _ = p₀.class B S hS (restrictionOfScalars B S hS x z).presheaf := hcls

end Main

end AlgebraicGeometry.Space

end
