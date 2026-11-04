module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors

/-!
# The stalk of a higher direct image is the colimit of the cohomology of the base changes

Let `f : X ⟶ Y` be a morphism of schemes, `F` an abelian sheaf on the small étale site of `X`
and `x` a geometric point of `Y`. By [Stacks, Tag 03Q8] the higher direct image `R^n f_* F` is
the sheafification of the presheaf `V ↦ H^n(X ×_Y V, F)` on `Y_étale`, and a stalk is unchanged
by sheafification, so

`(R^n f_* F)_x = colim_{(V, v)} H^n(X ×_Y V, F)`,

the colimit being over the category of étale neighbourhoods of `x`. This is the first step of the
proof of [Stacks, Tag 03Q9], here in the `AlgebraicGeometry.Scheme.Etale` model of the small
étale site — the model in which `Stacks.EtaleCohomology.smallEtaleStalkAb` and
`Stacks.EtaleCohomology.etaleAbelianDirectImage` are stated.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageCohomologyPresheaf` — the presheaf
  `V ↦ H^n(X ×_Y V, F)` on `Y_étale`.
* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkCocone` — the cocone on the diagram of
  those groups over the étale neighbourhoods of `x`, with vertex the stalk `(R^n f_* F)_x`.

## Relation to the registered statement

[Stacks, Tag 03Q9] itself, for `f` quasi-compact and quasi-separated over an arbitrary base and in
all three of its forms, is registered in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkHigherDirectImageStrictHenselization.lean`
(`AlgebraicGeometry.stalkHigherDirectImageIso`,
`AlgebraicGeometry.stalkDerivedPushforwardHomologyIso`,
`AlgebraicGeometry.stalkDerivedPushforwardIso`). The declarations below carry no tag attribute;
they are the stalk-of-the-cohomology-presheaf route, kept for their consumers.

## Main results

* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIso` — the stalk of `R^n f_* F` at `x`
  is the stalk of the cohomology presheaf, with no hypothesis on `f`, on `Y` or on `n`.
* `Stacks.EtaleCohomology.isColimitSmallEtaleHigherDirectImageStalkCocone` — **the first step of
  [Stacks, Tag 03Q9]**: that cocone is a colimit, so `(R^n f_* F)_x` is the filtered colimit of
  the `H^n(X ×_Y V, F)`.
* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoOfIsColimit` — **[Stacks, Tag 03Q9]
  over [Stacks, Tag 03Q6] as a named hypothesis**: any group exhibited as that colimit is the
  stalk.
* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial` and
  `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial` —
  **[Stacks, Tag 03Q9] with `h03Q6` discharged, where the étale neighbourhoods of `x` have an
  initial object `(V, v)`**: the stalk is then the single group `H^n(X ×_Y V, F)`, and
  `H^n(X_étale, F)` when `V` is moreover the final object of `Y_étale`. No form of Tag 03Q6 is
  used, and `f` is arbitrary.
* `Stacks.EtaleCohomology.isZero_smallEtaleStalkAb_rightDerived_etaleAbelianDirectImage` and
  `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_forall_affine_level` —
  **the unconditional vanishing form**: if the cohomology of `F` over every base change
  `X ×_Y V` vanishes then so does `R^n f_* F`, hence so does each of its stalks. No form of
  Tag 03Q6 is used.

## Implementation notes

**What is proved and what is carried.** The source's proof of [Stacks, Tag 03Q9] has three
steps: the stalk is the colimit of the cohomology presheaf (Tag 03Q8 and invariance of a stalk
under sheafification); `X ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the `X ×_S V`; and étale
cohomology carries that limit of schemes to the colimit of the cohomology groups, which is
[Stacks, Tag 03Q6]. The first step is proved here, unconditionally and in the model of the small
étale site that the tag's consumers use. The second is
`AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone`, which is stated in the *other*
model of the small étale site, the one built on `AlgebraicGeometry.BigEtaleSite`; the two models
are not identified in this library, so it is not applied here. The third is not available at the
shape Tag 03Q9 needs; see below.

`smallEtaleHigherDirectImageStalkIsoOfIsColimit` therefore carries, as the single hypothesis
`h03Q6`, a group together with a colimiting cocone of the diagram of the `H^n(X ×_Y V, F)`.
Supplying `H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)` for that group is exactly Tag 03Q6 at this
system together with the limit identification above; nothing here asserts it.

**Where `h03Q6` *is* discharged.** It is discharged, with no cohomological input at all, for
every pair `(Y, x)` whose category of étale neighbourhoods has an **initial** object `(V, v)`:
the colimit is then attained at that one index, by
`CategoryTheory.Limits.colimitOfDiagramTerminal`, and the vertex is the single group
`H^n(X ×_Y V, F)` — `smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial`. If `V` is moreover
the final object of `Y_étale` the base change `X ×_Y V` is `X` and the vertex is the étale
cohomology `H^n(X_étale, F)` — `smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial`. Both
hypotheses hold when `Y` is strictly henselian local at the image of `x` and `x` lies over the
closed point, by `Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement`; that
instance is `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint`.
An initial object of the index is also the limit of the diagram of the neighbourhoods themselves,
so there `Spec(𝒪^{sh}_{Y,x})` is `V` — in the strictly henselian instance `V` is the final object
and `Spec(𝒪^{sh}_{Y,x})` is `Y` — the limit `X ×_Y Spec(𝒪^{sh}_{Y,x})` of the base changes is
`X ×_Y V` itself, and Tag 03Q6 has no content. So this is a restriction on `(Y, x)`, not a step
towards the general case. What the general case still needs is set out next.

**Why the qcqs Tag 03Q6 does not supply `h03Q6`.** The library has Tag 03Q6 at the
source's quasi-compact quasi-separated generality,
`BaseChangeAlgebraSystem.etaleCohomologyColimit_baseChange_qcqs_etale_isColimit`, itself over
an explicitly named hypothesis `hdLimit` — the higher-degree Čech/Mayer--Vietoris descent from an
affine chart to a qcqs scheme. Three further things separate it from `h03Q6`, and each of them
alone is enough to stop the application. Its base is an *affine* `T = Spec A`,
whereas Tag 03Q9 ranges over an arbitrary base `S`. Its index is a nonempty *directed preorder*
of affine schemes over `T`, whereas the index here is the cofiltered *category* of étale
neighbourhoods of `x`. And its coefficients are a *given* system of abelian sheaves on the
levels, whereas Tag 03Q9 needs the system of inverse images `(X ×_S V ⟶ X)^{-1}F` of the single
sheaf `F` on `X`. So `h03Q6` is carried here in the form Tag 03Q9 consumes it rather than in the
form the library's Tag 03Q6 proves, and discharging it needs those three reductions as well as
`hdLimit`.

`hdLimit` is moreover *not* the thing to carry. It asserts `R^p Γ_W(-) ≅ H^p(site, -)` for a
chart `W` of the limit, which on any site is equivalent to terminality of the image of `W`; for a
non-affine `Y` it is **false**, not merely unproved, so that registration is vacuous there.
The implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/QcqsBaseChangeEtaleCohomology.lean`
record this, together with the obstruction
`Stacks.EtaleCohomology.QcqsBaseChange.subsingleton_globalSections_of_hdLimit_zero`, and
name the genuine remaining input of Tag 03Q6: [Stacks, Tag 09YP] over the terminal **sheaf**
rather than over an object of the colimit site.

**What the general `h03Q6` is waiting on.** Four things, none of which is in the library:

1. Tag 09YP over the terminal sheaf, which is the open half of Tag 03Q6 itself. The weak-system
   Tag 09YP that is available,
   `Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone`, computes the cohomology of
   `u_i(X)` for `X` an object of a level's site; the right hand side of Tag 03Q9 is the
   cohomology of the whole colimit site, which is that statement at the terminal sheaf.
2. The index. The diagram of `h03Q6` is indexed by
   `((AlgebraicGeometry.Scheme.pointSmallEtale x).fiber.Elements)ᵒᵖ`, the opposite of the category
   of elements of `(AlgebraicGeometry.Scheme.pointSmallEtale x).fiber : Y.Etale ⥤ Type u`,
   whereas the geometric half `AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone` is an
   `IsLimit` of a cone on
   `AlgebraicGeometry.etaleNeighborhoodBaseChangeDiagram B S hS s f :
   (AlgebraicGeometry.geometricPointFiber B S hS s).Elements ⥤ Scheme.{u}`, the elements of
   `AlgebraicGeometry.geometricPointFiber B S hS s : AlgebraicGeometry.SmallEtale B S hS ⥤ Type u`.
   `AlgebraicGeometry.SmallEtale B S hS` is the full subcategory of the étale objects of
   `AlgebraicGeometry.BigEtaleOver B S hS`, hence of the étale `S`-schemes that **belong to `B`**,
   i.e. have `Scheme.size < B.cutoff`; `Y.Etale` is all of them. So the two index categories are
   not the same category, and identifying them is not a formality: it is the statement that the
   `B`-bounded étale objects form a dense subsite of `Y_étale`, i.e. the comparison lemma, which
   this library does not prove. This is the `AlgebraicGeometry.BigEtaleSite` ↔
   `AlgebraicGeometry.Scheme.Etale` model identification, and it is the reason the vertex of
   `h03Q6` is left abstract rather than named `H^n(X ×_Y Spec(𝒪^{sh}_{Y,x}), p^{-1}F)`: the
   scheme `X ×_Y Spec(𝒪^{sh}_{Y,x})` exists in the library only as the vertex of that cone.
3. The coefficients. Tag 03Q6's system is a system of abelian sheaves on the small *affine* étale
   sites of the levels; the inverse images of one sheaf `F` on `X` form
   `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.baseChangeInverseImageSystem`, which lives on
   their small étale sites and has not been transported to the affine ones.
4. The base. Tag 03Q6 as proved is over an affine `T = Spec A`, Tag 03Q9 over an arbitrary `Y`.
   The affine étale neighbourhoods of `x` all lie over an affine open of `Y` containing its image,
   so this is the mildest of the four, but no such cofinality statement is in the library either.

So `h03Q6` is not blocked by a single missing lemma. It needs the open half of Tag 03Q6 (1), and
then the model identification (2) to state the answer at all; (3) and (4) are reductions on top of
those. Nothing below assumes any of it.

**Why the vanishing form needs no hypothesis.** `R^n f_* F` is the sheafification of the
cohomology presheaf, and a presheaf vanishing on a dense family of objects sheafifies to zero;
that is the sections criterion
`Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforward_of_isAffine_sections` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/NormalSepClosedConstantDirectImage.lean`.
So levelwise vanishing kills the sheaf outright, and a fortiori every stalk — the right hand
side of Tag 03Q9 then vanishes too, by Tag 03Q6, but the implication proved here does not pass
through it.

**Coefficients.** Abelian sheaves are taken with coefficients in `Ab.{u + 1}` for schemes in
`Scheme.{u}`, which is the universe `Stacks.EtaleCohomology.smallEtaleStalkAb` is pinned to and
the one the curve files use. The sheaf-level statements are stated at that universe for the same
reason; the sections criterion it rests on is universe-generic.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] smallEtalePushforward_additive

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify X.smallEtaleTopology Ab.{u + 1}]
  [HasSheafify Y.smallEtaleTopology Ab.{u + 1}]
  [HasInjectiveResolutions (Sheaf X.smallEtaleTopology Ab.{u + 1})]

/-- The cohomology presheaf `V ↦ H^n(X ×_Y V, F)` of [Stacks, Tag 03Q8] on the small étale site
of `Y`: the `n`-th right derived functor of the underlying presheaf of the direct image along
`f`, evaluated at `F`. Its value at `V` is identified with the `n`-th derived sections of `F`
over the base change `X ×_Y V` by
`Stacks.DerivedFunctor.rightDerivedEvaluationIso`. -/
abbrev smallEtaleHigherDirectImageCohomologyPresheaf
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℕ) : Y.Etaleᵒᵖ ⥤ Ab.{u + 1} :=
  (((etaleAbelianDirectImage.{u, u + 1} f ⋙
    sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1}).rightDerived n).obj F)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Y)
  (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℕ)

/-- **The stalk of a higher direct image is the stalk of the cohomology presheaf.** The higher
direct image `R^n f_* F` is the sheafification of the presheaf `V ↦ H^n(X ×_Y V, F)` by
[Stacks, Tag 03Q8], and the fibre functor of a point of a site does not change under
sheafification, so the two stalks at a geometric point `x` of `Y` agree.

No hypothesis is carried: `f` is an arbitrary morphism of schemes, `Y` an arbitrary scheme, `x`
an arbitrary geometric point and `n` an arbitrary degree. -/
def smallEtaleHigherDirectImageStalkIso :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      (Scheme.pointSmallEtale x).presheafFiber.obj
        (smallEtaleHigherDirectImageCohomologyPresheaf f F n) :=
  letI : (etaleAbelianDirectImage.{u, u + 1} f ⋙
      sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1}).Additive := ⟨by intros; rfl⟩
  letI : (presheafToSheaf Y.smallEtaleTopology Ab.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  -- Stacks 03Q8: `R^n f_*` is `R^n` of the underlying presheaf, sheafified; the sheafification
  -- counit identifies the composite with the direct image itself.
  (smallEtaleStalkAb x).mapIso
      ((DerivedFunctor.rightDerivedIso
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (etaleAbelianDirectImage.{u, u + 1} f)
              (asIso (sheafificationAdjunction Y.smallEtaleTopology Ab.{u + 1}).counit) ≪≫
            (etaleAbelianDirectImage.{u, u + 1} f).rightUnitor) n).symm.app F ≪≫
        (DerivedFunctor.rightDerivedEvaluationIso
          (etaleAbelianDirectImage.{u, u + 1} f ⋙
            sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1})
          (presheafToSheaf Y.smallEtaleTopology Ab.{u + 1}) F n).symm) ≪≫
    ((Scheme.pointSmallEtale x).presheafToSheafCompSheafFiberIso Ab.{u + 1}).app _

/-- The cocone on the diagram of the cohomology groups `H^n(X ×_Y V, F)` over the category of
étale neighbourhoods `(V, v)` of a geometric point `x` of `Y`, with vertex the stalk
`(R^n f_* F)_x`: the colimit cocone computing the stalk of the cohomology presheaf, transported
along `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIso`. -/
def smallEtaleHigherDirectImageStalkCocone :
    Cocone ((CategoryOfElements.π (Scheme.pointSmallEtale x).fiber).op ⋙
      smallEtaleHigherDirectImageCohomologyPresheaf f F n) :=
  ((Scheme.pointSmallEtale x).presheafFiberCocone
      (smallEtaleHigherDirectImageCohomologyPresheaf f F n)).extend
    (smallEtaleHigherDirectImageStalkIso f x F n).inv

/-- The vertex of `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkCocone` is the stalk
`(R^n f_* F)_x`. -/
@[simp]
theorem smallEtaleHigherDirectImageStalkCocone_pt :
    (smallEtaleHigherDirectImageStalkCocone f x F n).pt =
      (smallEtaleStalkAb x).obj
        (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) :=
  rfl

/-- **The first step of the proof of [Stacks, Tag 03Q9].** For an arbitrary morphism of schemes
`f : X ⟶ Y`, an arbitrary abelian sheaf `F` on the small étale site of `X`, an arbitrary
geometric point `x` of `Y` and an arbitrary degree `n`, the stalk `(R^n f_* F)_x` is the filtered
colimit of the cohomology groups `H^n(X ×_Y V, F)` over the category of étale neighbourhoods
`(V, v)` of `x`.

The source turns that colimit into the single group `H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)` by
writing the strict henselisation as the limit of the étale neighbourhoods and invoking
[Stacks, Tag 03Q6]; that step is not available here and nothing below assumes it. -/
@[sga "4 VIII 5.1" "partial", sga "4½ Arcata 2.3.3"]
def isColimitSmallEtaleHigherDirectImageStalkCocone :
    IsColimit (smallEtaleHigherDirectImageStalkCocone f x F n) :=
  IsColimit.ofIsoColimit
    ((Scheme.pointSmallEtale x).isColimitPresheafFiberCocone
      (smallEtaleHigherDirectImageCohomologyPresheaf f F n))
    (Cocones.ext (smallEtaleHigherDirectImageStalkIso f x F n).symm fun _ => rfl)

/-- **[Stacks, Tag 03Q9] over [Stacks, Tag 03Q6] as a named hypothesis.** For an arbitrary
morphism of schemes `f : X ⟶ Y`, an arbitrary geometric point `x` of `Y`, an arbitrary abelian
sheaf `F` on `X_étale` and an arbitrary degree `n`: any abelian group exhibited by `h03Q6` as the
colimit of the cohomology groups `H^n(X ×_Y V, F)` over the étale neighbourhoods of `x` is the
stalk `(R^n f_* F)_x`.

What is proved is the first step of the source's argument,
`Stacks.EtaleCohomology.isColimitSmallEtaleHigherDirectImageStalkCocone`. What `h03Q6` carries is
the identification of that colimit with a named group: in the source it is
`H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)`, and supplying it is [Stacks, Tag 03Q6] at the system
of base changes to the étale neighbourhoods of `x`, whose limit is
`X ×_S Spec(𝒪^{sh}_{S,s})`. -/
@[sga "4 VIII 5.1" "partial", sga "4½ Arcata 2.3.3"]
def smallEtaleHigherDirectImageStalkIsoOfIsColimit
    (c : Cocone ((CategoryOfElements.π (Scheme.pointSmallEtale x).fiber).op ⋙
      smallEtaleHigherDirectImageCohomologyPresheaf f F n))
    (h03Q6 : IsColimit c) :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      c.pt :=
  IsColimit.coconePointUniqueUpToIso (isColimitSmallEtaleHigherDirectImageStalkCocone f x F n)
    h03Q6

/-! ### `h03Q6` discharged where the étale neighbourhoods of `x` have an initial object -/

/-- **`h03Q6` at an initial étale neighbourhood.** If `(V, v)` is an initial object of the
category of étale neighbourhoods of `x` — equivalently a terminal object of the index of the
colimit — then the cocone of
`CategoryTheory.Limits.coconeOfDiagramTerminal`, whose vertex is the single group
`H^n(X ×_Y V, F)`, is a colimit cocone.

This is `CategoryTheory.Limits.colimitOfDiagramTerminal`: no cohomological input enters, because
the colimit is attained at one index. It is the hypothesis `h03Q6` of
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoOfIsColimit` supplied with a named
vertex, for those pairs `(Y, x)` whose neighbourhood category degenerates in this way. -/
def isColimitSmallEtaleHigherDirectImageCohomologyCoconeOfIsInitial
    {V : (Scheme.pointSmallEtale x).fiber.Elements} (hV : IsInitial V) :
    IsColimit (coconeOfDiagramTerminal hV.op
      ((CategoryOfElements.π (Scheme.pointSmallEtale x).fiber).op ⋙
        smallEtaleHigherDirectImageCohomologyPresheaf f F n)) :=
  colimitOfDiagramTerminal hV.op _

/-- **[Stacks, Tag 03Q9] where the étale neighbourhoods of `x` have an initial object `(V, v)`:
the stalk `(R^n f_* F)_x` is the single cohomology group `H^n(X ×_Y V, F)`.** For an arbitrary
morphism of schemes `f : X ⟶ Y`, an arbitrary abelian sheaf `F` on `X_étale` and an arbitrary
degree `n`; no quasi-compactness or quasi-separatedness of `f` is assumed.

Here `h03Q6` is discharged rather than carried: the filtered colimit of
`Stacks.EtaleCohomology.isColimitSmallEtaleHigherDirectImageStalkCocone` is attained at `(V, v)`.
Where the base is strictly henselian local at the image of `x`, so that `V` is the final object
of `Y_étale`, this is the source's statement at that base — the limit
`X ×_Y Spec(𝒪^{sh}_{Y,x})` of the base changes is then `X ×_Y V` itself; see
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial` and, for the
strictly henselian instance of it,
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint`.

What is **not** covered is the point of the tag, a base at which the neighbourhood category does
*not* degenerate: there the vertex is `H^n(X ×_Y Spec(𝒪^{sh}_{Y,x}), p^{-1}F)` for a scheme that
is a proper limit of the `X ×_Y V`, and identifying the colimit with its cohomology is
[Stacks, Tag 03Q6], which this does not touch. -/
def smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial
    {V : (Scheme.pointSmallEtale x).fiber.Elements} (hV : IsInitial V) :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      ((sheafToPresheaf X.smallEtaleTopology Ab.{u + 1} ⋙
        (evaluation X.Etaleᵒᵖ Ab.{u + 1}).obj
          (op ((smallEtaleBaseChange f).obj V.1))).rightDerived n).obj F :=
  smallEtaleHigherDirectImageStalkIsoOfIsColimit f x F n _
      (isColimitSmallEtaleHigherDirectImageCohomologyCoconeOfIsInitial f x F n hV) ≪≫
    letI : (etaleAbelianDirectImage.{u, u + 1} f ⋙
        sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1}).Additive := ⟨by intros; rfl⟩
    DerivedFunctor.rightDerivedEvaluationIso
      (etaleAbelianDirectImage.{u, u + 1} f ⋙ sheafToPresheaf Y.smallEtaleTopology Ab.{u + 1})
      ((evaluation Y.Etaleᵒᵖ Ab.{u + 1}).obj (op V.1)) F n

/-- **[Stacks, Tag 03Q9] where the initial étale neighbourhood of `x` is the final object of
`Y_étale`: the stalk `(R^n f_* F)_x` is the étale cohomology `H^n(X_étale, F)`.** The base change
`X ×_Y V` is then `X` itself, so the single group of
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial` is the `n`-th
derived global sections of `F` on `X_étale`: base change along `f` carries a terminal object of
`Y_étale` to a terminal object of `X_étale`
(`Stacks.EtaleCohomology.isTerminalSmallEtaleBaseChangeObj`), and derived sections over a
terminal object are derived global sections
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`).

The hypotheses hold when `Y` is strictly henselian local at the image of `x` and `x` lies over
the closed point; that instance is
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint`. -/
def smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial
    {V : (Scheme.pointSmallEtale x).fiber.Elements} (hV : IsInitial V) (hV' : IsTerminal V.1) :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      ((Sheaf.Γ X.smallEtaleTopology Ab.{u + 1}).rightDerived n).obj F :=
  smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial f x F n hV ≪≫
    (Stacks.DerivedFunctor.rightDerivedIso
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology Ab.{u + 1}
        (isTerminalSmallEtaleBaseChangeObj f hV') ≪≫
          sheafSectionsNatIsoEvaluation X.smallEtaleTopology Ab.{u + 1}) n).symm.app F

/-! ### The vanishing form, which needs no form of Tag 03Q6 -/

/-- **Levelwise vanishing kills the higher direct image.** If the `n`-th derived sections of `F`
over the base change `X ×_Y V` vanish for every object `V` of `Y_étale` with affine source, then
`R^n f_* F = 0`.

This is the sections criterion of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/NormalSepClosedConstantDirectImage.lean` read
through the direct image of this library's `Scheme.Etale` model. Together with
[Stacks, Tag 03Q6] it is the case of [Stacks, Tag 03Q9] in which the colimit computing the stalk
is a colimit of zero groups; but no form of Tag 03Q6 is used, the implication being Tag 03Q8 and
density of the affine objects alone. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_forall_affine_level
    (h : ∀ (V : Y.Etale) [IsAffine V.left],
      IsZero (((sheafToPresheaf X.smallEtaleTopology Ab.{u + 1} ⋙
        (evaluation X.Etaleᵒᵖ Ab.{u + 1}).obj
          (op ((smallEtaleBaseChange f).obj V))).rightDerived n).obj F)) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) :=
  isZero_rightDerived_smallEtalePushforward_of_isAffine_sections f F n fun V _ => h V

/-- **Levelwise vanishing kills every stalk of the higher direct image.** If the `n`-th derived
sections of `F` over the base change `X ×_Y V` vanish for every object `V` of `Y_étale` with
affine source, then the stalk of `R^n f_* F` at every geometric point of `Y` is zero.

This is the shape in which a consumer that needs only the vanishing of a stalk can take
[Stacks, Tag 03Q9]: the levelwise vanishing gives it outright. The curve files of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/` no longer need even that — the sheaf-level
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_forall_affine_level` just
above is enough for them — but the two are one step apart. -/
theorem isZero_smallEtaleStalkAb_rightDerived_etaleAbelianDirectImage
    (h : ∀ (V : Y.Etale) [IsAffine V.left],
      IsZero (((sheafToPresheaf X.smallEtaleTopology Ab.{u + 1} ⋙
        (evaluation X.Etaleᵒᵖ Ab.{u + 1}).obj
          (op ((smallEtaleBaseChange f).obj V))).rightDerived n).obj F)) :
    IsZero ((smallEtaleStalkAb x).obj
      (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F)) :=
  (smallEtaleStalkAb x).map_isZero
    (isZero_rightDerived_etaleAbelianDirectImage_of_forall_affine_level f F n h)

end Stacks.EtaleCohomology

end
