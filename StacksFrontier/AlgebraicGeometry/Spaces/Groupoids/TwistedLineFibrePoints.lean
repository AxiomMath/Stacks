module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedLineQuotient

/-!
# An infinite fibre of points over a field-valued point

Let `K` be a field of characteristic zero carrying a ring automorphism `σ` of infinite order,
and let the integers act on `Spec K` through `σ` and on the affine line `Spec K[t]` through
the twisted translation that acts on coefficients by `σ` and sends `t` to `t + 1`. Write
`Y = Spec K / ℤ` and `X = (Spec K[t]) / ℤ` for the two quotient sheaves and `Z = Spec K`.
The inclusion of the constants is equivariant, so it induces `f : X ⟶ Y`, and the square

```
Spec K[t] ----q----> Spec K
    |                  |
    p                  g
    v                  v
    X -------f-------> Y
```

is cartesian: `W = X ×_Y Z` is the affine line itself. Taking `x ∈ |X|` to be the image of
the origin `t = 0` and `z` the unique point of `|Z|`, the set

`F_{x,z} = {w ∈ |W| : p w = x and q w = z}`

of Stacks 0AC2 is then in bijection with `ℤ`, which is the content of Stacks 0AC4.

## Main definitions

* `AlgebraicGeometry.Space.twistedBaseSite` and `AlgebraicGeometry.Space.twistedLineSite` are
  `Spec K` and `Spec K[t]` as objects of a big fppf site over `S`, and
  `AlgebraicGeometry.Space.twistedLineToBaseSite`,
  `AlgebraicGeometry.Space.twistedBaseToLineSite` are the inclusion of the constants and the
  origin as morphisms of that site.
* `AlgebraicGeometry.Space.twistedOriginClass` is the point `t = 0` of the affine line and
  `AlgebraicGeometry.Space.twistedFibrePoint` is its `n`-th translate, the point `t = n`.
* `AlgebraicGeometry.Space.twistedFibreSet` is the set `F_{x,z}` of Stacks 0AC2 for this
  square, with `x` the image of the origin in the quotient and `z` the unique point of
  `Spec K`.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_twistedLineQuotient`: **Stacks 0AC4**, the
  square above is cartesian, so `W = Spec K[t]`. It is
  `AlgebraicGeometry.Space.exists_isPullback_toQuotientSheaf_twistedLine`, an instance of
  Stacks 07S3 for two actions related by an equivariant map, transported along
  `AlgebraicGeometry.Space.pointsYonedaIso` so that its upper row is the pair of represented
  presheaves whose point sets the fibre set lives in.
* `AlgebraicGeometry.Space.twistedFibreEquivInt`: **Stacks 0AC4**, `F_{x,z} = ℤ` as a set.
  Injectivity of `n ↦ (t = n)` is `AlgebraicGeometry.Space.twistedFibrePoint_injective`, which
  rests on the coordinate computation
  `AlgebraicGeometry.Space.appTop_twistedTranslate_origin_coord` and on characteristic zero;
  surjectivity is `AlgebraicGeometry.Space.twistedFibreSet_eq_range`, an instance of
  `AlgebraicGeometry.Space.exists_smul_of_pointsMap_actionProjection_eq`.

## Implementation notes

Stacks 0AC4 is an *example*: it exhibits a square (Stacks 0AC1) whose fibre set (Stacks 0AC2)
is infinite, and asserts nothing about the quotients beyond what the ambient section supplies.
Accordingly the two clauses formalized here are the cartesianness of the square and the
computation of the fibre set; the quotient sheaves are used only through their universal
property, and in particular no algebraicity of `X` or `Y` is needed for either clause.

`AlgebraicGeometry.Space.isAlgebraicSpace_twistedLineQuotient` and
`AlgebraicGeometry.Space.isAlgebraicSpace_twistedBaseQuotient` record that the two quotients
are algebraic spaces, which Stacks 0AC4 does not assert and neither clause uses; they carry the
two effective-descent hypotheses of
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`, exactly as the sibling example
Stacks 02Z1 does. Writing the fibre set as `AlgebraicGeometry.Space.fibrePoints` of a
`AlgebraicGeometry.Space.PointsFibresDiagram` would need those two together with the
algebraicity of the two schemes, which is
`AlgebraicGeometry.isAlgebraicSpace_yoneda`; the set here is by definition the set that
`AlgebraicGeometry.Space.fibrePoints` would produce from them.

The condition `q w = z` is vacuous because `|Spec K|` is a single point
(`AlgebraicGeometry.Space.subsingleton_points_yoneda_fieldSpec`); it is retained so that the
statement is literally the set of Stacks 0AC2.

## References

* [Stacks Project, Tag 0AC4](https://stacks.math.columbia.edu/tag/0AC4)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 03BW](https://stacks.math.columbia.edu/tag/03BW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Multiplicative Opposite Polynomial

universe u

namespace AlgebraicGeometry.Space

section Fibre

variable {K : Type u} [Field K] {S : Scheme.{u}} {B : BigFppfSite.{u}}
  (hS : B.Contains S) (hK : B.Contains (Spec (.of K)))
  (hL : B.Contains (Spec (.of K[X]))) (s : Spec (.of K) ⟶ S) (σ : K ≃+* K)
  (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- `Spec K`, as an object of a big fppf site over `S`. -/
abbrev twistedBaseSite : BigFppfOver B S hS := Over.mk (⟨s⟩ : B.obj hK ⟶ B.obj hS)

/-- The affine line `Spec K[t]`, as an object of a big fppf site over `S` through the
inclusion of the constants. -/
abbrev twistedLineSite : BigFppfOver B S hS :=
  Over.mk (⟨Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫ s⟩ : B.obj hL ⟶ B.obj hS)

/-- The inclusion of the constants `Spec K[t] ⟶ Spec K`, as a morphism of the site. -/
def twistedLineToBaseSite : twistedLineSite hS hL s ⟶ twistedBaseSite hS hK s :=
  (Over.post (X := B.obj hS) B.inclusion).preimage (twistedLineToBase s)

/-- The origin `t = 0`, as a morphism of the site. -/
def twistedBaseToLineSite : twistedBaseSite hS hK s ⟶ twistedLineSite hS hL s :=
  (Over.post (X := B.obj hS) B.inclusion).preimage (twistedBaseToLine s)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The inclusion of the constants, read as a morphism over `S`, is `twistedLineToBase`. -/
@[simp]
theorem post_map_twistedLineToBaseSite :
    (Over.post (X := B.obj hS) B.inclusion).map (twistedLineToBaseSite hS hK hL s) =
      twistedLineToBase s :=
  (Over.post (X := B.obj hS) B.inclusion).map_preimage _

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The origin, read as a morphism over `S`, is `twistedBaseToLine`. -/
@[simp]
theorem post_map_twistedBaseToLineSite :
    (Over.post (X := B.obj hS) B.inclusion).map (twistedBaseToLineSite hS hK hL s) =
      twistedBaseToLine s :=
  (Over.post (X := B.obj hS) B.inclusion).map_preimage _

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The origin, read as a morphism of schemes. -/
@[simp]
theorem toScheme_map_twistedBaseToLineSite :
    (BigFppfOver.toScheme B S hS).map (twistedBaseToLineSite hS hK hL s) =
      (twistedBaseToLine s).left :=
  congrArg Over.Hom.left (post_map_twistedBaseToLineSite hS hK hL s)

/-- The twisted action of the integers on the affine line, read on the object of the site. -/
abbrev twistedLineSiteAction :
    Multiplicative ℤ →* Aut (underlyingOver B hS (twistedLineSite hS hL s)) :=
  twistedLineAction s σ hs

/-- The action of the integers on `Spec K` through the powers of `σ`, read on the object of
the site. -/
abbrev twistedBaseSiteAction :
    Multiplicative ℤ →* Aut (underlyingOver B hS (twistedBaseSite hS hK s)) :=
  twistedBaseAction s σ hs

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The automorphism of the affine line realizing the `n`-th translation, read as a morphism
of schemes. -/
@[simp]
theorem toScheme_map_siteActionHom_twistedLine (g : Multiplicative ℤ) :
    (BigFppfOver.toScheme B S hS).map
        (siteActionHom (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
          (twistedLineSiteAction hS hL s σ hs) g) =
      (twistedLineAction s σ hs g).asIso.hom.left :=
  congrArg Over.Hom.left (post_map_siteActionHom (Multiplicative ℤ) B hS
    (twistedLineSite hS hL s) (twistedLineSiteAction hS hL s σ hs) g)

/-- The projection of the affine line onto its quotient by the twisted translations, the map
`p` of the square of Stacks 0AC4. -/
abbrev twistedLineProjection :
    yoneda.obj (twistedLineSite hS hL s) ⟶
      actionQuotient (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
        (twistedLineSiteAction hS hL s σ hs) :=
  actionProjection (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
    (twistedLineSiteAction hS hL s σ hs)

/-! ### The square is cartesian -/

/-- The projection of `Spec K` onto its quotient by the powers of `σ`, the map `g` of the
square of Stacks 0AC4. -/
abbrev twistedBaseProjection :
    yoneda.obj (twistedBaseSite hS hK s) ⟶
      actionQuotient (Multiplicative ℤ) B hS (twistedBaseSite hS hK s)
        (twistedBaseSiteAction hS hK s σ hs) :=
  actionProjection (Multiplicative ℤ) B hS (twistedBaseSite hS hK s)
    (twistedBaseSiteAction hS hK s σ hs)

/-- The square of Stacks 0AC4 in the shape in which the quotient sheaf is constructed, with
the restricted functors of points of the affine line and of `Spec K` as its upper row. -/
theorem exists_isPullback_toQuotientSheaf_twistedLine [CharZero K] (hσ : orderOf σ = 0) :
    ∃ f : (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (actionRelation (underlyingOver B hS (twistedLineSite hS hL s))
          (Multiplicative ℤ) (twistedLineSiteAction hS hL s σ hs))).obj ⟶
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (actionRelation (underlyingOver B hS (twistedBaseSite hS hK s))
          (Multiplicative ℤ) (twistedBaseSiteAction hS hK s σ hs))).obj,
      IsPullback
        (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (actionRelation (underlyingOver B hS (twistedLineSite hS hL s))
            (Multiplicative ℤ) (twistedLineSiteAction hS hL s σ hs)))
        ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post B.inclusion).map (twistedLineToBaseSite hS hK hL s))))
        f
        (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (actionRelation (underlyingOver B hS (twistedBaseSite hS hK s))
            (Multiplicative ℤ) (twistedBaseSiteAction hS hK s σ hs))) :=
  exists_isPullback_toQuotientSheaf_actionQuotient (Multiplicative ℤ) B hS
    (twistedLineSiteAction hS hL s σ hs) (twistedBaseSiteAction hS hK s σ hs)
    (twistedLineAction_actsNontrivially s σ hs) (twistedBaseAction_actsNontrivially s σ hs hσ)
    (twistedLineToBaseSite hS hK hL s)
    (fun g ↦ by
      rw [post_map_twistedLineToBaseSite]
      exact twistedLineToBase_comp_twistedBaseAction s σ hs g)

/-- **Stacks 0AC4**, the square. The projections of the affine line and of `Spec K` onto their
quotients by the twisted actions and the inclusion of the constants form a cartesian square, so
the fibre product `W = X ×_Y Z` of the example is the affine line `Spec K[t]` itself.

This is `AlgebraicGeometry.Space.exists_isPullback_toQuotientSheaf_twistedLine` transported
along `AlgebraicGeometry.Space.pointsYonedaIso`, which identifies the restricted functor of
points of an object of the site with the presheaf it represents; it is stated at the
represented presheaves because those are the corners whose point sets
`AlgebraicGeometry.Space.twistedFibreSet` is a subset of. -/
@[stacks 0AC4 "the square is cartesian, with W the affine line"]
theorem exists_isPullback_twistedLineQuotient [CharZero K] (hσ : orderOf σ = 0) :
    ∃ f : actionQuotient (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
        (twistedLineSiteAction hS hL s σ hs) ⟶
      actionQuotient (Multiplicative ℤ) B hS (twistedBaseSite hS hK s)
        (twistedBaseSiteAction hS hK s σ hs),
      IsPullback (twistedLineProjection hS hL s σ hs)
        (yoneda.map (twistedLineToBaseSite hS hK hL s)) f
        (twistedBaseProjection hS hK s σ hs) := by
  obtain ⟨f, hf⟩ := exists_isPullback_toQuotientSheaf_twistedLine hS hK hL s σ hs hσ
  refine ⟨f, hf.of_iso'
    (Space.pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion)
      (twistedLineSite hS hL s)).symm (Iso.refl _)
    (Space.pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion)
      (twistedBaseSite hS hK s)).symm (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · simp [twistedLineProjection, actionProjection]
  · have hq := pointsYonedaIso_inv_comp (Over.post (X := B.obj hS) B.inclusion)
      ((Over.post B.inclusion).map (twistedLineToBaseSite hS hK hL s))
    rw [Functor.preimage_map] at hq
    rw [Iso.symm_hom, ← hq]
    simp
  · simp
  · simp [twistedBaseProjection, actionProjection]

/-! ### The two quotients are algebraic spaces

Stacks 0AC4 asserts neither of the two statements of this section: it exhibits a square of the
shape (0AC1) and computes its fibre set, and both of those are proved without any algebraicity.
They are recorded because the example sits in a section about diagrams of algebraic spaces, and
because they show where the algebraicity of the quotients does and does not bite. The two
hypotheses are exactly those of
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` — Stacks 0265 reduced to effective
descent along a covering sieve for the two morphism properties it needs — and are carried as
hypotheses in the same way as for the sibling example Stacks 02Z1,
`AlgebraicGeometry.isAlgebraicSpace_involutionQuotient`. -/

/-- The quotient `X = A¹_K/ℤ` of Stacks 0AC4 is an algebraic space over `S`, given effective
descent along covering sieves for the two morphism properties of Stacks 0265. -/
theorem isAlgebraicSpace_twistedLineQuotient [CharZero K]
    (hdiag : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (hchart : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS (actionQuotient (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
      (twistedLineSiteAction hS hL s σ hs)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (twistedLineSite hS hL s)) := by
    change IsAffine (Spec (CommRingCat.of K[X]))
    infer_instance
  have := actionRelation_isEtaleEquivalenceRelation
    (underlyingOver B hS (twistedLineSite hS hL s)) (Multiplicative ℤ)
    (twistedLineSiteAction hS hL s σ hs) (twistedLineAction_actsNontrivially s σ hs)
  exact isAlgebraicSpace_quotientSheaf B S hS (twistedLineSite hS hL s)
    (actionRelation (underlyingOver B hS (twistedLineSite hS hL s)) (Multiplicative ℤ)
      (twistedLineSiteAction hS hL s σ hs)) hdiag hchart

/-- The quotient `Y = Spec K/ℤ` of Stacks 0AC4 is an algebraic space over `S`, given effective
descent along covering sieves for the two morphism properties of Stacks 0265. -/
theorem isAlgebraicSpace_twistedBaseQuotient (hσ : orderOf σ = 0)
    (hdiag : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (hchart : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS (actionQuotient (Multiplicative ℤ) B hS (twistedBaseSite hS hK s)
      (twistedBaseSiteAction hS hK s σ hs)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (twistedBaseSite hS hK s)) := by
    change IsAffine (Spec (CommRingCat.of K))
    infer_instance
  have := actionRelation_isEtaleEquivalenceRelation
    (underlyingOver B hS (twistedBaseSite hS hK s)) (Multiplicative ℤ)
    (twistedBaseSiteAction hS hK s σ hs) (twistedBaseAction_actsNontrivially s σ hs hσ)
  exact isAlgebraicSpace_quotientSheaf B S hS (twistedBaseSite hS hK s)
    (actionRelation (underlyingOver B hS (twistedBaseSite hS hK s)) (Multiplicative ℤ)
      (twistedBaseSiteAction hS hK s σ hs)) hdiag hchart

/-! ### The coordinate of a translate of the origin -/

/-- The `n`-th twisted translate of the origin pulls the coordinate of the affine line back to
the integer `n`, and this persists after precomposition with a morphism of field spectra. -/
theorem appTop_twistedTranslate_origin_coord {Ω : Type u} [Field Ω]
    (F : Spec (.of Ω) ⟶ Spec (.of K)) (n : ℤ) :
    (F ≫ (twistedBaseToLine s).left ≫
        (twistedLineAction s σ hs (ofAdd n)).asIso.hom.left).appTop (twistedLineCoord K) =
      (n : Γ(Spec (.of Ω), ⊤)) := by
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    twistedLineAction_appTop_coord s σ hs n, map_add,
    twistedBaseToLine_appTop_coord s, map_intCast, zero_add]

/-- Two twisted translates of the origin which become equal after precomposition with
morphisms of field spectra translate by the same integer: the coordinate of the `n`-th
translate is `n`, and in characteristic zero distinct integers stay distinct in every field
receiving `K`. -/
theorem twistedTranslate_origin_inj [CharZero K] {Ω : Type u} [Field Ω]
    (F G : Spec (.of Ω) ⟶ Spec (.of K)) {n m : ℤ}
    (h : F ≫ (twistedBaseToLine s).left ≫ (twistedLineAction s σ hs (ofAdd n)).asIso.hom.left =
      G ≫ (twistedBaseToLine s).left ≫ (twistedLineAction s σ hs (ofAdd m)).asIso.hom.left) :
    n = m := by
  have hcast : ((n : ℤ) : Γ(Spec (.of Ω), ⊤)) = ((m : ℤ) : Γ(Spec (.of Ω), ⊤)) :=
    ((appTop_twistedTranslate_origin_coord s σ hs F n).symm.trans
      (congrArg (fun k : Spec (.of Ω) ⟶ Spec (.of K[X]) ↦
        k.appTop (twistedLineCoord K)) h)).trans
      (appTop_twistedTranslate_origin_coord s σ hs G m)
  have hnt : Nontrivial Γ(Spec (.of Ω), ⊤) :=
    (Scheme.ΓSpecIso (.of Ω)).hom.hom.domain_nontrivial
  have hinj : Function.Injective
      (F.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) :=
    RingHom.injective _
  refine Int.cast_injective (α := K) (hinj ?_)
  rw [map_intCast, map_intCast]
  exact hcast

/-! ### The fibre of points over the image of the origin -/

/-- The field-valued point of the affine line given by the `n`-th twisted translate of the
origin, that is, by the point `t = n`. -/
def twistedFibreFieldPoint (n : ℤ) :
    FieldValuedPoint B S hS (yoneda.obj (twistedLineSite hS hL s)) where
  carrier := K
  contained := hK
  toBase := s
  value := twistedBaseToLineSite hS hK hL s ≫
    siteActionHom (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
      (twistedLineSiteAction hS hL s σ hs) (ofAdd n)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The morphism of `twistedFibreFieldPoint n` is the origin followed by the action of `n`. -/
@[simp]
theorem twistedFibreFieldPoint_value (n : ℤ) :
    (twistedFibreFieldPoint hS hK hL s σ hs n).value =
      twistedBaseToLineSite hS hK hL s ≫
        siteActionHom (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
          (twistedLineSiteAction hS hL s σ hs) (ofAdd n) := rfl

/-- The field-valued point of the affine line given by the origin `t = 0`. -/
def twistedOriginFieldPoint :
    FieldValuedPoint B S hS (yoneda.obj (twistedLineSite hS hL s)) where
  carrier := K
  contained := hK
  toBase := s
  value := twistedBaseToLineSite hS hK hL s

/-- The point `t = 0` of the affine line. -/
abbrev twistedOriginClass : points B S hS (yoneda.obj (twistedLineSite hS hL s)) :=
  (twistedOriginFieldPoint hS hK hL s).class B S hS _

/-- The point `t = n` of the affine line, the `n`-th twisted translate of the origin. -/
abbrev twistedFibrePoint (n : ℤ) : points B S hS (yoneda.obj (twistedLineSite hS hL s)) :=
  (twistedFibreFieldPoint hS hK hL s σ hs n).class B S hS _

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The point `t = n` is the image of the origin under the `n`-th translation. -/
theorem twistedFibrePoint_eq_pointsMap (n : ℤ) :
    twistedFibrePoint hS hK hL s σ hs n =
      pointsMap B S hS _ (yoneda.map (siteActionHom (Multiplicative ℤ) B hS
        (twistedLineSite hS hL s) (twistedLineSiteAction hS hL s σ hs) (ofAdd n)))
        (twistedOriginClass hS hK hL s) := rfl

/-- The set `F_{x,z}` of Stacks 0AC2 for the square of Stacks 0AC4: the points of the affine
line whose image in the quotient is the image `x` of the origin and whose image in `Spec K` is
its unique point `z`. -/
def twistedFibreSet : Set (points B S hS (yoneda.obj (twistedLineSite hS hL s))) :=
  {w | pointsMap B S hS _ (twistedLineProjection hS hL s σ hs) w =
        pointsMap B S hS _ (twistedLineProjection hS hL s σ hs)
          (twistedOriginClass hS hK hL s) ∧
      pointsMap B S hS _ (yoneda.map (twistedLineToBaseSite hS hK hL s)) w =
        pointsMap B S hS _ (yoneda.map (twistedLineToBaseSite hS hK hL s))
          (twistedOriginClass hS hK hL s)}

/-- Every translate of the origin lies in the fibre: the projection onto the quotient is
invariant under the action, and `|Spec K|` is a single point. -/
theorem twistedFibrePoint_mem (n : ℤ) :
    twistedFibrePoint hS hK hL s σ hs n ∈ twistedFibreSet hS hK hL s σ hs := by
  have hsub := subsingleton_points_yoneda_fieldSpec B S hS K hK s
  refine ⟨?_, Subsingleton.elim _ _⟩
  rw [twistedFibrePoint_eq_pointsMap, ← Function.comp_apply
      (f := pointsMap B S hS _ (twistedLineProjection hS hL s σ hs)), ← pointsMap_comp,
    siteActionHom_comp_actionProjection]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- Distinct integers give distinct points of the affine line. -/
theorem twistedFibrePoint_injective [CharZero K] :
    Function.Injective (twistedFibrePoint hS hK hL s σ hs) := by
  intro n m hnm
  obtain ⟨r, ⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS _ _ _).mp hnm
  have hf' : f ≫ (twistedFibreFieldPoint hS hK hL s σ hs n).value = r.value := hf
  have hg' : g ≫ (twistedFibreFieldPoint hS hK hL s σ hs m).value = r.value := hg
  have hmap (k : ℤ) :
      (BigFppfOver.toScheme B S hS).map (twistedFibreFieldPoint hS hK hL s σ hs k).value =
        (twistedBaseToLine s).left ≫ (twistedLineAction s σ hs (ofAdd k)).asIso.hom.left := by
    have h1 := (BigFppfOver.toScheme B S hS).map_comp (twistedBaseToLineSite hS hK hL s)
      (siteActionHom (Multiplicative ℤ) B hS (twistedLineSite hS hL s)
        (twistedLineSiteAction hS hL s σ hs) (ofAdd k))
    rw [toScheme_map_twistedBaseToLineSite, toScheme_map_siteActionHom_twistedLine] at h1
    exact h1
  have hcomp (k : ℤ) {Y : BigFppfOver B S hS} (u : Y ⟶ twistedBaseSite hS hK s)
      (v : Y ⟶ twistedLineSite hS hL s)
      (hu : u ≫ (twistedFibreFieldPoint hS hK hL s σ hs k).value = v) :
      (BigFppfOver.toScheme B S hS).map u ≫ (twistedBaseToLine s).left ≫
        (twistedLineAction s σ hs (ofAdd k)).asIso.hom.left =
      (BigFppfOver.toScheme B S hS).map v := by
    rw [← hmap k]
    exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans (congrArg _ hu)
  exact twistedTranslate_origin_inj s σ hs (Ω := r.carrier) _ _
    ((hcomp n f _ hf').trans (hcomp m g _ hg').symm)

/-- The fibre is exactly the orbit of the origin: Stacks 03BW for the twisted action, in the
form `AlgebraicGeometry.Space.exists_smul_of_pointsMap_actionProjection_eq`, says that a point
of the affine line with the same image in the quotient as the origin is a translate of it. -/
theorem twistedFibreSet_eq_range [CharZero K] :
    twistedFibreSet hS hK hL s σ hs = Set.range (twistedFibrePoint hS hK hL s σ hs) := by
  refine Set.Subset.antisymm (fun w hw ↦ ?_) (fun w hw ↦ ?_)
  · obtain ⟨g, hg⟩ := exists_smul_of_pointsMap_actionProjection_eq (Multiplicative ℤ) B hS
      (twistedLineSite hS hL s) (twistedLineSiteAction hS hL s σ hs)
      (twistedLineAction_actsNontrivially s σ hs) w (twistedOriginClass hS hK hL s) hw.1
    refine ⟨g.toAdd, ?_⟩
    rw [twistedFibrePoint_eq_pointsMap, ofAdd_toAdd]
    exact hg.symm
  · obtain ⟨n, rfl⟩ := hw
    exact twistedFibrePoint_mem hS hK hL s σ hs n

/-- **Stacks 0AC4**, the fibre. The set `F_{x,z}` of Stacks 0AC2 for the square of Stacks 0AC4
is in bijection with `ℤ`: the points `t = n` of the affine line all have the same image in the
quotient by the twisted translations and the same image in `Spec K`, they are pairwise
distinct because the coordinate of `t = n` is `n` and `K` has characteristic zero, and every
point of the fibre is one of them. -/
@[stacks 0AC4 "the fibre of points is the integers"]
def twistedFibreEquivInt [CharZero K] : twistedFibreSet hS hK hL s σ hs ≃ ℤ :=
  (Equiv.ofBijective
    (fun n : ℤ ↦ (⟨twistedFibrePoint hS hK hL s σ hs n,
        twistedFibrePoint_mem hS hK hL s σ hs n⟩ : twistedFibreSet hS hK hL s σ hs))
    ⟨fun _ _ h ↦ twistedFibrePoint_injective hS hK hL s σ hs (Subtype.ext_iff.mp h),
      fun w ↦ by
        obtain ⟨n, hn⟩ : w.1 ∈ Set.range (twistedFibrePoint hS hK hL s σ hs) := by
          rw [← twistedFibreSet_eq_range hS hK hL s σ hs]
          exact w.2
        exact ⟨n, Subtype.ext hn⟩⟩).symm

end Fibre

end AlgebraicGeometry.Space

end
