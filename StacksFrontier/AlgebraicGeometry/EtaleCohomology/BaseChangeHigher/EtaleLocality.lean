module

public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic

/-!
# Étale locality of invertibility, and the local squares of a base-change diagram

Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S`
factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and let

```
Uᵢ <--hᵢ-- Uᵢ ×_X Y
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Vᵢ ×_S T
```

be the induced squares.  This file assembles the inputs of the étale-local criterion for a
base-change map on small étale sites (Stacks 0EZR): the locality of invertibility, the two
identifications displayed in its proof, and the fact that the local square is cartesian.

The *locality of invertibility* says that a morphism of sheaves on the small étale site of a
scheme `X`, with values in an arbitrary category, is invertible as soon as its restriction to
the small étale site of each member of a family of étale morphisms covering `X` is invertible.
Mathlib's `CategoryTheory.Sheaf.isIso_of_coversTop` is the same statement with the covering
hypothesis phrased through `CategoryTheory.GrothendieckTopology.overPullback`, i.e. through the
slice site `X_étale/U`; what is added here is the passage to the small étale site of the scheme
`U` itself, which is the form in which the source states its hypothesis and the form in which
the rest of the étale development spells restriction.

The *local square* is a consequence of the data, not an extra hypothesis: it is
`Stacks.EtaleCohomology.isPullback_localSquare` below.  The morphism `eᵢ` is likewise
determined, by the two compatibilities the source implicitly uses, and is constructed here as
`Stacks.EtaleCohomology.localSquareDiag`.

The *two identifications* are `(h_* G)|_{Uᵢ} = h_{ᵢ,*}(G|_{Uᵢ ×_X Y})`, proved here for an
arbitrary cartesian square and arbitrary coefficients, and `(f^{-1} G)|_{Uᵢ} = f_ᵢ^{-1}(G|_{Vᵢ})`,
proved here for abelian coefficients, which is where the inverse image is available.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleObj` — an étale morphism `j : U ⟶ X` as an object of the
  small étale site of `X`.
* `Stacks.EtaleCohomology.etaleRestrictionAt` — restriction along an étale morphism, at an
  arbitrary coefficient category.
* `Stacks.EtaleCohomology.localSquareDiag` — the diagonal morphism `eᵢ : Uᵢ ×_X Y ⟶ Vᵢ ×_S T`
  of the local square.
* `AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeIsoOfIsPullback` — for an arbitrary
  cartesian square with one side étale, the comparison of the two composite functors of small
  étale sites around it.
* `Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback` — the identification
  `(h_* G)|_U = h_{U,*}(G|_{U ×_X Y})`, for an arbitrary cartesian square and arbitrary
  coefficients.
* `Stacks.EtaleCohomology.etaleAbelianRestrictionPushforwardIsoOfIsPullback` — the same for
  abelian coefficients, in the names the abelian étale development uses.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionFactorizationIso` — the
  identification `(f^{-1} G)|_U = f_U^{-1}(G|_V)` attached to a factorization `U → V → S` of
  `U → X → S` through an étale `V → S`, for abelian coefficients.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_etaleRestrictionAt` — **locality of invertibility
  on the small étale site**, at arbitrary coefficients.
* `Stacks.EtaleCohomology.isIso_of_isIso_etaleAbelianInverseImage_of_coversTop` — the same for
  abelian coefficients, with the hypothesis phrased through the inverse image rather than
  through restriction, which is the form in which the base-change map is stated.
* `Stacks.EtaleCohomology.isPullback_localSquare` — the local square is cartesian.
* `Stacks.EtaleCohomology.isPullback_localSquare_toBase` — the upper left corner of the local
  square is also the fibre product `Uᵢ ×_S T`, which is the identification the source uses to
  recognise the local square.
* `Stacks.EtaleCohomology.etale_of_isPullback_snd` — the projection of a cartesian square
  opposite an étale morphism is étale.

## Implementation notes

`etaleRestrictionAt` is stated for an arbitrary coefficient category because every ingredient of
it is: restriction is `Functor.sheafPushforwardContinuous` along composition with `j`, which
needs only continuity of that site functor.  The abelian and set-valued cases already in the
library, `Stacks.EtaleCohomology.etaleRestriction` and
`Stacks.EtaleCohomology.etaleRestrictionSets`, are the instantiations at
`AddCommGrpCat.{max (u + 1) v}` and `Type (max (u + 1) v)`; they are definitionally this functor
and are left untouched.  The name avoids `smallEtaleRestriction`, which in this library already
denotes the restriction functor of a *different* model of the small étale site, the one built on
`AlgebraicGeometry.BigEtaleSite` rather than on `AlgebraicGeometry.Scheme.Etale`; the two models
are not identified here.

Invertibility is transported from `smallEtaleObj j` to an arbitrary object of `X_étale` lying
over it along an isomorphism rather than an equality of objects: an object of `X.Etale` with a
morphism to `smallEtaleObj j` has the same underlying scheme as its descent along `j`, but the
two are equal only after rewriting the structure morphism, so the comparison is taken as
`CategoryTheory.MorphismProperty.Over.isoMk` on the identity, exactly as
`AlgebraicGeometry.Scheme.Etale.composeDescendIso` does.

The inverse image needs sheafification, so the identification of restriction with the inverse
image along an étale morphism, and with it the second of the two displayed identifications, is
available only at coefficients admitting sheafification; it is recorded at the abelian
coefficients `AddCommGrpCat.{max (u + 1) v}` of the rest of the étale abelian development.

## How these results combine

Stacks 0EZR has three parts, each concluding that a base-change comparison for the outer square
is invertible: for a sheaf, for an object of the unbounded derived category, and for the higher
direct images.  Each of the three reduces to the same equation, that the restriction to `Uᵢ` of
the base-change comparison of the outer square is, through the two identifications proved above,
the base-change comparison of the local square.  The comparison in question,
`Stacks.EtaleCohomology.etaleAbelianBaseChange`, is the mate of the identification of the two
composite inverse images around the square, so that equation is an instance of the pasting law
for mates, `Stacks.Cohomology.DerivedBaseChangePasting.mate_twoSquare_paste`; the analogous
development for quasi-coherent modules on the Zariski site, where the same steps are carried out,
is `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeSquare_pasteBase` together with
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.pushforwardSquare_pasteBase`.  The derived and
higher parts need in addition the compatibility of that equation with the derived functors, for
which the unbounded derived base-change comparison
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` is available.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w v u t

namespace Stacks.EtaleCohomology

/-! ### Restriction along an étale morphism -/

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- An étale morphism `j : U ⟶ X`, read as an object of the small étale site of `X`. -/
abbrev smallEtaleObj : X.Etale :=
  MorphismProperty.Over.mk (P := @Etale) ⊤ j inferInstance

/-- The underlying scheme of `smallEtaleObj j` is the source of `j`. -/
@[simp]
theorem smallEtaleObj_left : (smallEtaleObj j).left = U := rfl

/-- The structure morphism of `smallEtaleObj j` to `X` is `j` itself. -/
@[simp]
theorem smallEtaleObj_hom : (smallEtaleObj j).hom = j := rfl

variable (A : Type w) [Category.{v} A]

/-- Restriction along an étale morphism `j : U ⟶ X`, from sheaves on the small étale site of
`X` to sheaves on the small étale site of `U`, with values in an arbitrary category: on sections
it is precomposition with composition by `j`, so `(G|_U)(V) = G(V)` for `V` étale over `U`.

This is the functor written `G ↦ G|_U` in Stacks 0EZR.  The library's abelian and set-valued
restrictions, `Stacks.EtaleCohomology.etaleRestriction` and
`Stacks.EtaleCohomology.etaleRestrictionSets`, are its instantiations. -/
abbrev etaleRestrictionAt :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  (smallEtaleCompose j).sheafPushforwardContinuous A U.smallEtaleTopology X.smallEtaleTopology

/-- The sections of `G|_U` over an object `V` of the small étale site of `U` are the sections of
`G` over `V` regarded as a scheme étale over `X`. -/
theorem etaleRestrictionAt_obj_val_obj (G : Sheaf X.smallEtaleTopology A) (V : U.Etale) :
    ((etaleRestrictionAt j A).obj G).obj.obj (op V) =
      G.obj.obj (op ((smallEtaleCompose j).obj V)) :=
  rfl

/-- An object of the small étale site of `X` equipped with a morphism to `smallEtaleObj j`,
read as an object of the small étale site of `U`: its underlying scheme is unchanged and its
structure morphism to `U` is the given morphism. -/
abbrev descendOver {Z : X.Etale} (g : Z ⟶ smallEtaleObj j) : U.Etale :=
  MorphismProperty.Over.mk (P := @Etale) ⊤ g.left
    (by exact (inferInstance : Etale (g.left : Z.left ⟶ (smallEtaleObj j).left)))

/-- Composition with `j` returns `descendOver j g` to the object it came from.  The underlying
morphism of schemes is the identity; only the structure morphism to `X` has been rewritten,
using that `g` is a morphism over `X`. -/
def descendOverIso {Z : X.Etale} (g : Z ⟶ smallEtaleObj j) :
    (smallEtaleCompose j).obj (descendOver j g) ≅ Z :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans (MorphismProperty.Over.w g).symm)

end Restriction

/-! ### Locality of invertibility -/

section Locality

variable {X : Scheme.{u}} {A : Type w} [Category.{v} A]
  {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
  {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) [∀ i, Etale (u i)]

/-- If the restriction of `φ` to the small étale site of `U i` is invertible, then every
component of `φ` at an object of `X_étale` lying over `U i` is invertible.  The object is
identified with the image under composition by `u i` of its descent, and the component is
transported along that isomorphism. -/
theorem isIso_app_of_isIso_etaleRestrictionAt (i : ι)
    (h : IsIso ((etaleRestrictionAt (u i) A).map φ)) {Z : X.Etale}
    (g : Z ⟶ smallEtaleObj (u i)) : IsIso (φ.hom.app (op Z)) := by
  have hV : IsIso (φ.hom.app (op ((smallEtaleCompose (u i)).obj (descendOver (u i) g)))) :=
    (NatTrans.isIso_iff_isIso_app _).mp
      ((ObjectProperty.isIso_hom_iff _).mpr h) (op (descendOver (u i) g))
  have : IsIso (φ.hom.app (op Z) ≫ G.obj.map (descendOverIso (u i) g).hom.op) := by
    rw [← φ.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.obj.map (descendOverIso (u i) g).hom.op)

/-- **Invertibility of a morphism of sheaves is local on the small étale site.**  Let `φ` be a
morphism of sheaves with values in an arbitrary category on the small étale site of a scheme
`X`, and let `{u i : U i ⟶ X}` be a family of étale morphisms whose associated objects cover
the final object of `X_étale` — that is, an étale covering of `X`.  If the restriction of `φ`
to the small étale site of each `U i` is invertible, then `φ` is invertible.

This is the final step of the proof of Stacks 0EZR: a base-change map which restricts to an
isomorphism over every member of an étale covering is an isomorphism. -/
theorem isIso_of_isIso_etaleRestrictionAt
    (hcov : X.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (u i))
    (h : ∀ i, IsIso ((etaleRestrictionAt (u i) A).map φ)) : IsIso φ := by
  refine Sheaf.isIso_of_coversTop hcov fun i ↦ ?_
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  exact isIso_app_of_isIso_etaleRestrictionAt φ u i (h i) W.unop.hom

/-- **Invertibility of a morphism of sheaves on the small étale site is exactly a local
condition.**  The converse of `isIso_of_isIso_etaleRestrictionAt` is trivial, restriction
being a functor. -/
theorem isIso_iff_isIso_etaleRestrictionAt
    (hcov : X.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (u i)) :
    IsIso φ ↔ ∀ i, IsIso ((etaleRestrictionAt (u i) A).map φ) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_isIso_etaleRestrictionAt φ u hcov⟩

end Locality

section LocalityAbelian

variable {X : Scheme.{u}}
  {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) t}} (φ : F ⟶ G)
  {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X) [∀ i, Etale (u i)]

/-- **Invertibility of a morphism of abelian sheaves on the small étale site is local**, with
the hypothesis phrased through the inverse image along each `u i` rather than through
restriction.  The two agree along `Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`
for an étale morphism, and the inverse image is the form in which base-change maps on the small
étale sites are stated. -/
theorem isIso_of_isIso_etaleAbelianInverseImage_of_coversTop
    (hcov : X.smallEtaleTopology.CoversTop fun i ↦ smallEtaleObj (u i))
    (h : ∀ i, IsIso ((etaleAbelianInverseImage.{u, t} (u i)).map φ)) : IsIso φ :=
  isIso_of_isIso_etaleRestrictionAt φ u hcov fun i ↦
    (NatIso.isIso_map_iff (etaleAbelianInverseImageRestrictionIso.{u, t} (u i)) φ).mp (h i)

end LocalityAbelian

/-! ### The local square of a base-change diagram -/

section LocalSquare

variable {X Y S T U V YU TV : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  {j : U ⟶ X} {v : V ⟶ S} {fU : U ⟶ V} {hU : YU ⟶ U} {pY : YU ⟶ Y} {gV : TV ⟶ V} {pT : TV ⟶ T}

/-- The diagonal morphism `eᵢ : Uᵢ ×_X Y ⟶ Vᵢ ×_S T` of the local square of Stacks 0EZR.  It is
the morphism into the fibre product `Vᵢ ×_S T` determined by `hᵢ ≫ fᵢ` and by the projection to
`Y` followed by `e`; the source writes it down without comment, and it is the unique morphism
compatible with both projections. -/
def localSquareDiag (sq : IsPullback h e f g) (hfac : fU ≫ v = j ≫ f)
    (upper : IsPullback hU pY j h) (lower : IsPullback gV pT v g) : YU ⟶ TV :=
  lower.lift (hU ≫ fU) (pY ≫ e)
    (calc (hU ≫ fU) ≫ v = hU ≫ j ≫ f := by rw [Category.assoc, hfac]
      _ = (pY ≫ h) ≫ f := by rw [← Category.assoc, upper.w]
      _ = (pY ≫ e) ≫ g := by rw [Category.assoc, sq.w, Category.assoc])

/-- The diagonal of the local square followed by the projection `Vᵢ ×_S T ⟶ Vᵢ` is the
projection to `Uᵢ` followed by `fᵢ`: the local square commutes. -/
@[simp]
theorem localSquareDiag_comp_fst (sq : IsPullback h e f g) (hfac : fU ≫ v = j ≫ f)
    (upper : IsPullback hU pY j h) (lower : IsPullback gV pT v g) :
    localSquareDiag sq hfac upper lower ≫ gV = hU ≫ fU :=
  lower.lift_fst _ _ _

/-- The diagonal of the local square followed by the projection `Vᵢ ×_S T ⟶ T` is the projection
to `Y` followed by `e`: the diagonal lies over `e`. -/
@[simp]
theorem localSquareDiag_comp_snd (sq : IsPullback h e f g) (hfac : fU ≫ v = j ≫ f)
    (upper : IsPullback hU pY j h) (lower : IsPullback gV pT v g) :
    localSquareDiag sq hfac upper lower ≫ pT = pY ≫ e :=
  lower.lift_snd _ _ _

/-- **The local square of Stacks 0EZR is cartesian.**  Given the cartesian square
`Y = X ×_S T`, a morphism `j : U ⟶ X` whose composite to `S` factors through `v : V ⟶ S`, and
the two fibre products `YU = U ×_X Y` and `TV = V ×_S T`, the square

```
U <--hU-- YU
|fU       |eᵢ
V <--gV-- TV
```

is cartesian.  The source asserts this as part of the data ("consider the cartesian
diagrams"); it is derived here, so that no hypothesis beyond the source's is carried.  The
argument is the standard cancellation: pasting this square with `TV = V ×_S T` on the right
gives the square `YU = U ×_S T` of
`Stacks.EtaleCohomology.isPullback_localSquare_toBase`, rewritten along the factorization, and
a square whose paste with a cartesian square is cartesian is itself cartesian.

Neither étaleness of `j` nor of `v` is used, so this holds for an arbitrary factorization. -/
theorem isPullback_localSquare (sq : IsPullback h e f g) (hfac : fU ≫ v = j ≫ f)
    (upper : IsPullback hU pY j h) (lower : IsPullback gV pT v g) :
    IsPullback hU (localSquareDiag sq hfac upper lower) fU gV := by
  refine IsPullback.of_bot (h₃₁ := g) ?_ ?_ lower
  · rw [localSquareDiag_comp_snd, hfac]
    exact upper.paste_vert sq
  · rw [localSquareDiag_comp_fst]

end LocalSquare

end Stacks.EtaleCohomology

/-! ### The site square of an arbitrary cartesian square with one side étale -/

namespace AlgebraicGeometry.Scheme.Etale

section

variable {X Y U YU : Scheme.{u}} {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y}

/-- The projection of a cartesian square to the side opposite an étale morphism is étale. -/
theorem etale_of_isPullback_snd (upper : IsPullback hU pY j h) : Etale pY :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback upper inferInstance

/-- For an arbitrary cartesian square of schemes

```
YU --pY--> Y
|hU        |h
U  --j-->  X
```

with `j` étale, composition with `j` followed by base change along `h` agrees with base change
along `hU` followed by composition with `pY`, as functors of small étale sites.  On an object `V`
of the small étale site of `U` the two sides are `V ×_X Y` and `V ×_U YU`, and the comparison is
the canonical isomorphism of the two cartesian squares.

`AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeIso` is the case where the square is
the chosen pullback square. -/
def smallEtaleComposeBaseChangeIsoOfIsPullback (upper : IsPullback hU pY j h) :
    haveI := etale_of_isPullback_snd upper
    smallEtaleCompose j ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange h ≅
      Stacks.EtaleCohomology.smallEtaleBaseChange hU ⋙ smallEtaleCompose pY := by
  haveI := etale_of_isPullback_snd upper
  apply Functor.fullyFaithfulCancelRight (Scheme.Etale.forget Y)
  calc (smallEtaleCompose j ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange h) ⋙
        Scheme.Etale.forget Y
      = Scheme.Etale.forget U ⋙ (CategoryTheory.Over.map j ⋙ CategoryTheory.Over.pullback h) :=
        rfl
    _ ≅ Scheme.Etale.forget U ⋙
          (CategoryTheory.Over.pullback hU ⋙ CategoryTheory.Over.map pY) :=
        Functor.isoWhiskerLeft _ (overPullbackBaseChangeIso pY hU h j upper.flip)
    _ = (Stacks.EtaleCohomology.smallEtaleBaseChange hU ⋙ smallEtaleCompose pY) ⋙
          Scheme.Etale.forget Y := rfl

end

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

/-! ### Restriction and direct image around an arbitrary cartesian square -/

section RestrictionPushforward

variable {X Y U YU : Scheme.{u}} {h : Y ⟶ X} {j : U ⟶ X} [Etale j] {hU : YU ⟶ U} {pY : YU ⟶ Y}
  (A : Type w) [Category.{v} A]

/-- **The identification `(h_* G)|_U = h_{U,*}(G|_{YU})` of Stacks 0EZR**, for an arbitrary
cartesian square of schemes

```
YU --pY--> Y
|hU        |h
U  --j-->  X
```

with `j` étale, and for sheaves valued in an arbitrary category.

This is the second of the two identifications displayed in the proof of Stacks 0EZR: restricting
the direct image along `h` to the small étale site of `U` is the direct image along the base
change `hU` of the restriction to the small étale site of `YU`.  Stacks obtains it from Sites,
Lemma 7.28.2 (Tag 03EF), the compatibility of direct image with localization; here both sides
are direct images along a composite of continuous functors of small étale sites, and the two
composites are identified by `smallEtaleComposeBaseChangeIsoOfIsPullback`.

`Stacks.EtaleCohomology.smallEtaleRestrictionPushforwardBaseChangeIso` is the case where the
square is the chosen pullback square. -/
def etaleRestrictionPushforwardIsoOfIsPullback (upper : IsPullback hU pY j h) :
    haveI := etale_of_isPullback_snd upper
    etaleRestrictionAt pY A ⋙
        (smallEtaleBaseChange hU).sheafPushforwardContinuous A
          U.smallEtaleTopology YU.smallEtaleTopology ≅
      (smallEtaleBaseChange h).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology ⋙
        etaleRestrictionAt j A := by
  haveI := etale_of_isPullback_snd upper
  have := Functor.isContinuous_comp (smallEtaleCompose j) (smallEtaleBaseChange h)
    U.smallEtaleTopology X.smallEtaleTopology Y.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousComp'
      (smallEtaleComposeBaseChangeIsoOfIsPullback upper).symm A
      U.smallEtaleTopology YU.smallEtaleTopology Y.smallEtaleTopology ≪≫
    (Functor.sheafPushforwardContinuousComp (smallEtaleCompose j) (smallEtaleBaseChange h) A
      U.smallEtaleTopology X.smallEtaleTopology Y.smallEtaleTopology).symm

/-- **The identification `(h_* G)|_U = h_{U,*}(G|_{YU})` for abelian sheaves**, in the names the
abelian étale development uses: it is `etaleRestrictionPushforwardIsoOfIsPullback` at the
coefficients `AddCommGrpCat.{max (u + 1) t}`, both sides being definitionally the same
functors. -/
def etaleAbelianRestrictionPushforwardIsoOfIsPullback (upper : IsPullback hU pY j h) :
    haveI := etale_of_isPullback_snd upper
    etaleRestriction.{u, t} pY ⋙ etaleAbelianDirectImage.{u, t} hU ≅
      etaleAbelianDirectImage.{u, t} h ⋙ etaleRestriction.{u, t} j :=
  haveI := etale_of_isPullback_snd upper
  etaleRestrictionPushforwardIsoOfIsPullback AddCommGrpCat.{max (u + 1) t} upper

end RestrictionPushforward

/-! ### Restriction and inverse image through an étale factorization -/

section InverseImageFactorization

variable {X S U V : Scheme.{u}} {f : X ⟶ S} {j : U ⟶ X} [Etale j] {v : V ⟶ S} [Etale v]
  {fU : U ⟶ V}

/-- **The identification `(f^{-1} G)|_U = f_U^{-1}(G|_V)` of Stacks 0EZR**, for abelian sheaves.
Let `f : X ⟶ S`, let `j : U ⟶ X` and `v : V ⟶ S` be étale, and let `fU : U ⟶ V` be a
factorization of `U ⟶ X ⟶ S` through `v`.  Restricting the inverse image along `f` to the small
étale site of `U` is the inverse image along `fU` of the restriction to the small étale site of
`V`.

This is the first of the two identifications displayed in the proof of Stacks 0EZR, and the
source's own argument for it: both sides are the inverse image along the common composite
`U ⟶ S`, because restriction along an étale morphism *is* the inverse image along it
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`) and the inverse image of a
composite is the composite of the inverse images
(`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso`). -/
def etaleAbelianInverseImageRestrictionFactorizationIso (hfac : fU ≫ v = j ≫ f) :
    etaleAbelianInverseImage.{u, t} f ⋙ etaleRestriction.{u, t} j ≅
      etaleRestriction.{u, t} v ⋙ etaleAbelianInverseImage.{u, t} fU :=
  Functor.isoWhiskerLeft (etaleAbelianInverseImage.{u, t} f)
      (etaleAbelianInverseImageRestrictionIso.{u, t} j).symm ≪≫
    (etaleAbelianInverseImageCompIso.{u, t} j f).symm ≪≫
    eqToIso (congrArg (fun k : U ⟶ S ↦ etaleAbelianInverseImage.{u, t} k) hfac.symm) ≪≫
    etaleAbelianInverseImageCompIso.{u, t} fU v ≪≫
    Functor.isoWhiskerRight (etaleAbelianInverseImageRestrictionIso.{u, t} v)
      (etaleAbelianInverseImage.{u, t} fU)

end InverseImageFactorization

end Stacks.EtaleCohomology

end
