module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafRepresentable

/-!
# The morphism of ringed topoi of a 1-morphism of representable categories (Stacks 075J)

Let `p : 𝒳 ⥤ (Sch/S)` and `q : 𝒴 ⥤ (Sch/S)` be categories over the big fppf category of a
scheme `S`, let `F : 𝒳 ⥤ 𝒴` be a 1-morphism between them, and suppose `p` is representable by an
object `X` of `(Sch/S)` and `q` by an object `Y`, i.e. each is equivalent over `(Sch/S)` to a
slice (Stacks 02Y3). Then `F` *is* a morphism of schemes `g : X ⟶ Y` over `S`: read through the
two representing equivalences `e` and `d`, the 1-morphism
`e⁻¹ ⋙ F ⋙ d : (Sch/S)/X ⥤ (Sch/S)/Y` is, on the nose, `CategoryTheory.Over.map g`. Hence the
morphism of ringed topoi `F : (Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴)` of Stacks 06TW agrees, under the
identifications of Stacks 075I, with the morphism of ringed topoi
`g : (Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)` attached to the morphism of schemes, for any
topology `τ` on the underlying category of schemes which is coarser than the fppf one.

"Agrees" is read as the source reads it: the two morphisms of ringed topoi are the two sides of
the square of representing sites, so the agreement is the statement that the square commutes.
Composing with the morphism of ringed topoi of `e⁻¹` on the left and with that of `d` on the
right turns `F` into a morphism of ringed topoi
`(Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)`, which is where `g` lives, and the agreement
asserts of those two that their inverse images are identified by a canonical comparison and that
their structure maps correspond under it. The comparison is canonical because the equality
`e⁻¹ ⋙ F ⋙ d = Over.map g` of 1-morphisms of slices makes the two inverse images the same
restriction functor, so the comparison is the transport along that equality and nothing is
chosen. It is an agreement of *ringed* topoi: the structure-map statement is an equation between
morphisms of sheaves of commutative rings.

## The direction the equality goes

The square

```
𝒳 --F--> 𝒴
e|        |d
(Sch/S)/X --Over.map g--> (Sch/S)/Y
```

does *not* commute on the nose, and cannot: going round it the other way inserts
`e ⋙ e⁻¹`, which is only isomorphic to the identity. It is the square with `e⁻¹` on the left
that commutes strictly, and that is the form stated in
`AlgebraicGeometry.Stack.eq_map_representingObjectHom`. The original square commutes up to the
2-isomorphism `AlgebraicGeometry.Stack.representableBySquareIso`, whose components come from the
unit of `e` and therefore lie over identities of `(Sch/S)`; that last point is
`AlgebraicGeometry.Stack.whiskerRight_representableBySquareIso_hom`, so the square 2-commutes in
the 2-category of categories fibred in groupoids *over* `(Sch/S)`, not merely in `Cat`.

## Main definitions

* `CategoryTheory.Over.homOfCompForgetEq`: the morphism `X ⟶ Y` carried by a functor
  `Over X ⥤ Over Y` which commutes strictly with the two slice projections.
* `AlgebraicGeometry.Stack.representingObjectHom`: **Stacks 075J**, the morphism of schemes
  `X ⟶ Y` over `S` corresponding to the 1-morphism `F`.
* `AlgebraicGeometry.Stack.representableBySquareIso`: **Stacks 075J**, the 2-isomorphism filling
  the square above.
* `AlgebraicGeometry.Stack.representingObjectRingedToposHom`: **Stacks 075J**, the morphism of
  ringed topoi `(Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)` of the morphism of schemes.
* `AlgebraicGeometry.Stack.conjugatedRingedToposHom`: **Stacks 075J**, the morphism of ringed
  topoi `F : (Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴)` of Stacks 06TW read on the representing sites.
* `AlgebraicGeometry.Stack.conjugatedRingedToposHomInverseImageIso`: the canonical comparison of
  the inverse images of those two morphisms of ringed topoi.

## Main results

* `CategoryTheory.Over.eq_map_homOfCompForgetEq`: a functor between slices commuting strictly
  with the slice projections *is* `CategoryTheory.Over.map` of the morphism it carries.
* `AlgebraicGeometry.Stack.eq_map_representingObjectHom`: **Stacks 075J**, the 1-morphism of
  slices obtained from `F` by the two representing equivalences is the one induced by the
  morphism of schemes.
* `AlgebraicGeometry.Stack.whiskerRight_representableBySquareIso_hom`: **Stacks 075J**, the
  2-isomorphism filling the square is a 2-cell over `(Sch/S)`.
* `AlgebraicGeometry.Stack.associatedRingedToposHom_congr`: the morphism of ringed topoi of
  Stacks 06TW depends on its 1-morphism only.
* `AlgebraicGeometry.Stack.fSharpInverseImage_conjugatedRingedToposHom`: **Stacks 075J**, the two
  morphisms of ringed topoi agree — their inverse images are identified by the canonical
  comparison, and their structure maps correspond under it as morphisms of sheaves of
  commutative rings.
* `AlgebraicGeometry.Stack.fSharp_conjugatedRingedToposHom`: **Stacks 075J**, the same agreement
  in the direct-image form in which a morphism of ringed topoi states its structure map.
* `AlgebraicGeometry.Stack.essentiallySmall_of_representableBy`: a representable category fibred
  in groupoids is essentially small at the universe of the big site.
* `AlgebraicGeometry.Stack.isTransport_fSharpInverseImageForget_associatedRingedToposHom`: the
  structure map of the morphism of ringed topoi of Stacks 06TW is, on underlying sheaves of sets,
  the canonical identification of the two structure sheaves and nothing else.
* `AlgebraicGeometry.Stack.associatedRingedToposHom_representingObjectHom`: the congruence
  of 1-morphisms of slices that the agreement rests on.

## Implementation notes

`CategoryTheory.Over.eq_map_homOfCompForgetEq` is the only non-formal step. A functor
`G : 𝒞/X ⥤ 𝒞/Y` with `G ⋙ Over.forget Y = Over.forget X` leaves the domain of an object
untouched, so the structure map of `G.obj (X --𝟙--> X)` is a morphism `X ⟶ Y`; that is `g`. For
an arbitrary `T` the unique morphism `T ⟶ (X --𝟙--> X)` of `𝒞/X` — the terminal object — has
`T.hom` underneath it, so functoriality forces the structure map of `G.obj T` to be
`T.hom ≫ g`, which is the structure map of `(Over.map g).obj T`. Objects of a slice are equal
once their domains and structure maps are
(`CategoryTheory.CostructuredArrow.obj_ext`), and morphisms once their underlying morphisms are
(`CategoryTheory.Over.OverMorphism.ext`), so `CategoryTheory.Functor.ext` finishes.

As in `AlgebraicGeometry.Stack.structureSheaf` the topology argument is an arbitrary topology
coarser than the fppf one; the five statements of the source are its values at the five big
topologies. Essential smallness at the universe in which the structure sheaf takes its sections
is what `AlgebraicGeometry.Stack.associatedRingedToposHom` needs for its direct image to exist;
for the two slices it is supplied by `EssentiallySmall.{u} B.Schemes`, which is Stacks 000J
(`AlgebraicGeometry.essentiallySmall_schemeBelow`), as an instance hypothesis exactly as in
`StacksFrontier/AlgebraicGeometry/Stacks/EssentiallySmallSite.lean`. For `𝒳` and `𝒴` themselves it
is *not* assumed: it follows from representability by
`AlgebraicGeometry.Stack.essentiallySmall_of_representableBy`, and the two statements of the
agreement introduce it that way rather than as a hypothesis.

The statements about the 1-morphisms of slices assume neither `p.IsFiberedInGroupoids` nor
`q.IsFiberedInGroupoids`, although the source assumes both: being representable means being
equivalent over `(Sch/S)` to a slice, and a slice is fibred in groupoids, so the two assumptions
are consequences of the representability hypotheses rather than extra input. Dropping them there
is a generalization, not a weakening. The statements about ringed topoi do take them, because
`AlgebraicGeometry.Stack.associatedRingedToposHom` is stated for a category fibred in groupoids
and takes the witness as an argument; they are the source's own hypotheses on `𝒳` and `𝒴`.
Likewise `F` is taken to be strictly over the base, `F ⋙ q = p`, which together
with fibredness in groupoids of the target is the same thing as being a 1-morphism of fibred
categories (`CategoryTheory.Functor.IsFiberedInGroupoids.isFibredOneMorphism`), and is the
condition `StacksRepresentableCFG.MorphismOver` records.

The transport to the representing sites is by composition of morphisms of ringed topoi
(`AlgebraicGeometry.RingedToposHom.comp`, Stacks 01D3 part (3)), not by applying
`AlgebraicGeometry.Stack.associatedRingedToposHom` to the composite 1-morphism
`e⁻¹ ⋙ F ⋙ d`. The two have the same inverse image — restriction of sheaves composes on the
nose, `CategoryTheory.Functor.sheafPushforwardContinuousComp` being `Iso.refl` — but a morphism
of topoi names its adjunction, and the adjunction of a composite of morphisms of topoi is
`CategoryTheory.Adjunction.comp` of the three, not the adjunction
`CategoryTheory.Functor.IsFibredOneMorphism.sheafAdjunctionInheritedTopology` builds for the
composite 1-morphism. So the two morphisms of ringed topoi are not equal as terms, and the
honest statement is the one about the composite, which is also the one the source makes: the
composite is what "`F` read through the identifications" means.

For the same reason the agreement cannot be an equality of morphisms of ringed topoi: the two
sides of the square have inverse images that are equal, but the structure maps live over
different presentations and the comparison has to appear. It appears as
`AlgebraicGeometry.Stack.conjugatedRingedToposHomInverseImageIso`, and the two statements of the
agreement are the two readings of "the structure maps correspond under it" that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposSquare.lean` provides: the
inverse-image reading on sheaves of commutative rings
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_eq_of_isTransport`) and the direct-image
reading through the adjoint mate (`AlgebraicGeometry.RingedToposHom.ringedSquare_of_isTransport`).

Both are proved by the transport calculus of `Stacks.IsTransport` rather than by computing a
2-cell: each of the four morphisms of ringed topoi in sight has, on underlying sheaves of sets,
`eqToHom` of an identification of structure sheaves for its structure map
(`AlgebraicGeometry.Stack.isTransport_fSharpInverseImageForget_associatedRingedToposHom`), the
comparison of the inverse images is `eqToHom` of the equality of the two restriction functors,
and two transports between the same objects are equal.

## References

* [Stacks Project, Tag 075J](https://stacks.math.columbia.edu/tag/075J)
* [Stacks Project, Tag 075I](https://stacks.math.columbia.edu/tag/075I)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 02Y3](https://stacks.math.columbia.edu/tag/02Y3)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback

namespace CategoryTheory.Over

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- A functor between slices commuting strictly with the slice projections does not move the
domain of an object. -/
theorem left_obj_of_comp_forget_eq {G : Over X ⥤ Over Y}
    (h : G ⋙ Over.forget Y = Over.forget X) (T : Over X) : (G.obj T).left = T.left :=
  congrArg (fun K : Over X ⥤ C => K.obj T) h

/-- The morphism `X ⟶ Y` carried by a functor `G : 𝒞/X ⥤ 𝒞/Y` commuting strictly with the slice
projections: the structure map of the image of the terminal object `X --𝟙--> X`, whose domain is
`X` by `CategoryTheory.Over.left_obj_of_comp_forget_eq`. -/
def homOfCompForgetEq {G : Over X ⥤ Over Y} (h : G ⋙ Over.forget Y = Over.forget X) : X ⟶ Y :=
  eqToHom (left_obj_of_comp_forget_eq h (Over.mk (𝟙 X))).symm ≫ (G.obj (Over.mk (𝟙 X))).hom

/-- The structure map of the image of an object `T` under a functor between slices commuting
strictly with the slice projections is `T.hom` followed by the morphism the functor carries: the
unique morphism from `T` to the terminal object of `𝒞/X` has `T.hom` underneath it. -/
theorem hom_obj_of_comp_forget_eq {G : Over X ⥤ Over Y}
    (h : G ⋙ Over.forget Y = Over.forget X) (T : Over X) :
    (G.obj T).hom =
      eqToHom (left_obj_of_comp_forget_eq h T) ≫ T.hom ≫ homOfCompForgetEq h := by
  have hw := Over.w (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 X)))
  have hm := Functor.congr_hom h (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 X))
  simp only [Functor.comp_map, Over.forget_map, Over.homMk_left] at hm
  rw [← hw, hm, homOfCompForgetEq]
  simp

/-- A functor `𝒞/X ⥤ 𝒞/Y` commuting strictly with the slice projections *is* postcomposition
with the morphism `X ⟶ Y` it carries. -/
theorem eq_map_homOfCompForgetEq {G : Over X ⥤ Over Y}
    (h : G ⋙ Over.forget Y = Over.forget X) : G = Over.map (homOfCompForgetEq h) := by
  have hobj : ∀ T : Over X, G.obj T = (Over.map (homOfCompForgetEq h)).obj T := fun T =>
    CostructuredArrow.obj_ext _ _ (left_obj_of_comp_forget_eq h T)
      (by simpa using (hom_obj_of_comp_forget_eq h T).symm)
  refine Functor.ext hobj fun T T' φ => Over.OverMorphism.ext ?_
  have hm := Functor.congr_hom h φ
  simp only [Functor.comp_map, Over.forget_map] at hm
  simp [hm]

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (X Y : BigFppfOver B S hS)
  (e : StacksRepresentableCFG.RepresentableBy p X)
  (d : StacksRepresentableCFG.RepresentableBy q Y)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- Reading a 1-morphism `F` through the two representing equivalences gives a functor between
the slices `(Sch/S)/X` and `(Sch/S)/Y` which commutes strictly with their projections to
`(Sch/S)`: all three of `e⁻¹`, `F` and `d` do. -/
theorem comp_forget_eq_of_representableBy (hF : F ⋙ q = p) :
    (e.inv.functor ⋙ F ⋙ d.hom.functor) ⋙ Over.forget Y = Over.forget X := by
  rw [Functor.assoc, Functor.assoc, d.hom.w, hF, e.inv.w]

/-- **Stacks 075J.** The morphism of schemes `X ⟶ Y` over `S` corresponding to a 1-morphism
`F : 𝒳 ⥤ 𝒴` of categories representable by `X` and by `Y`: the morphism carried by the functor
of slices that `F` becomes under the two representing equivalences. -/
@[stacks 075J "the corresponding morphism of schemes"]
def representingObjectHom (hF : F ⋙ q = p) : X ⟶ Y :=
  Over.homOfCompForgetEq (comp_forget_eq_of_representableBy B S hS p q F X Y e d hF)

/-- **Stacks 075J.** Read through the two representing equivalences, the 1-morphism `F` *is*
postcomposition with the corresponding morphism of schemes `g : X ⟶ Y`, as an equality of
functors `(Sch/S)/X ⥤ (Sch/S)/Y`. -/
@[stacks 075J "the 1-morphism of slices is the one of the morphism of schemes"]
theorem eq_map_representingObjectHom (hF : F ⋙ q = p) :
    e.inv.functor ⋙ F ⋙ d.hom.functor =
      Over.map (representingObjectHom B S hS p q F X Y e d hF) :=
  Over.eq_map_homOfCompForgetEq _

/-- **Stacks 075J.** The square formed by `F`, the two representing equivalences and
postcomposition with the corresponding morphism of schemes 2-commutes: its 2-cell is the unit of
the representing equivalence of `X`, whiskered with `F ⋙ d`. -/
@[stacks 075J "the square of 1-morphisms 2-commutes"]
def representableBySquareIso (hF : F ⋙ q = p) :
    F ⋙ d.hom.functor ≅
      e.hom.functor ⋙ Over.map (representingObjectHom B S hS p q F X Y e d hF) :=
  Functor.isoWhiskerRight e.unitIso (F ⋙ d.hom.functor) ≪≫
    eqToIso (by rw [Functor.assoc, eq_map_representingObjectHom])

/-- **Stacks 075J.** The 2-cell filling the square is a 2-cell *over* `(Sch/S)`: whiskering it
with the projection of `(Sch/S)/Y` gives the identity 2-cell. So the square 2-commutes in the
2-category of categories fibred in groupoids over `(Sch/S)`, which is where the comparison of
Stacks 075I takes place. -/
@[stacks 075J "the 2-cell of the square is over the base"]
theorem whiskerRight_representableBySquareIso_hom (hF : F ⋙ q = p) :
    Functor.whiskerRight (representableBySquareIso B S hS p q F X Y e d hF).hom
        (Over.forget Y) =
      eqToHom (by
        rw [Functor.assoc, d.hom.w, hF, Functor.assoc, Over.mapForget_eq, e.hom.w]) := by
  refine NatTrans.ext (funext fun a => ?_)
  simp only [representableBySquareIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, Functor.map_comp,
    eqToHom_map, Functor.comp_map]
  have h1 := Functor.congr_hom d.hom.w (F.map (e.unitIso.hom.app a))
  have h2 := Functor.congr_hom hF (e.unitIso.hom.app a)
  have h3 := NatTrans.congr_app e.unit_over a
  simp only [Functor.whiskerRight_app, eqToHom_app] at h3
  simp only [Functor.comp_map] at h1 h2
  rw [h1, h2, h3]
  simp

/-- The morphism of ringed topoi of Stacks 06TW depends on its 1-morphism only: the hypothesis
that the 1-morphism is one of fibred categories is a proposition, so equal 1-morphisms give
equal morphisms of ringed topoi. -/
theorem associatedRingedToposHom_congr [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]
    {F₁ F₂ : 𝒳 ⥤ 𝒴} (h : F₁ = F₂)
    (hF₁ : p.IsFibredOneMorphism q F₁) (hF₂ : p.IsFibredOneMorphism q F₂) :
    associatedRingedToposHom B S hS p q F₁ hp hq τ hτ hF₁ =
      associatedRingedToposHom B S hS p q F₂ hp hq τ hτ hF₂ := by
  subst h
  rfl

/-- A 1-morphism of categories fibred in groupoids over the big site, strictly compatible with
the projections, is continuous for the associated topologies. -/
private theorem isContinuous_associatedTopology_of_comp_eq {𝒜 ℬ : Type*} [Category 𝒜]
    [Category ℬ] {P : 𝒜 ⥤ BigFppfOver B S hS} {Q : ℬ ⥤ BigFppfOver B S hS} {G : 𝒜 ⥤ ℬ}
    (hP : P.IsFiberedInGroupoids) (hQ : Q.IsFiberedInGroupoids) (hG : G ⋙ Q = P) :
    G.IsContinuous (associatedTopology B S hS P τ) (associatedTopology B S hS Q τ) := by
  have := hP.isFibered
  have := hQ.isFibered
  exact ((hQ.isFibredOneMorphism hG).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1

section RingedTopoi

variable [EssentiallySmall.{u} B.Schemes]

/-- A congruence of 1-morphisms of slices, not the comparison of Stacks 075J: the morphism of
ringed topoi (Stacks 06TW) of the 1-morphism `e⁻¹ ⋙ F ⋙ d` of slices is the one of
postcomposition with the corresponding morphism of schemes, because the two 1-morphisms are the
same functor (`AlgebraicGeometry.Stack.eq_map_representingObjectHom`). Both sides are morphisms
`(Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)`; neither is the morphism of ringed topoi
`(Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴)` that Stacks 075J compares, for which see
`AlgebraicGeometry.Stack.fSharpInverseImage_conjugatedRingedToposHom`. -/
theorem associatedRingedToposHom_representingObjectHom (hF : F ⋙ q = p) :
    associatedRingedToposHom B S hS (Over.forget X) (Over.forget Y)
        (e.inv.functor ⋙ F ⋙ d.hom.functor) (.over_forget X) (.over_forget Y) τ hτ
        ((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism
          (comp_forget_eq_of_representableBy B S hS p q F X Y e d hF)) =
      associatedRingedToposHom B S hS (Over.forget X) (Over.forget Y)
        (Over.map (representingObjectHom B S hS p q F X Y e d hF))
        (.over_forget X) (.over_forget Y) τ hτ
        ((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism
          (Over.mapForget_eq (representingObjectHom B S hS p q F X Y e d hF))) :=
  associatedRingedToposHom_congr B S hS (Over.forget X) (Over.forget Y) (.over_forget X)
    (.over_forget Y) τ hτ (eq_map_representingObjectHom B S hS p q F X Y e d hF) _ _

include e in
/-- A category fibred in groupoids representable by an object `X` of the big site is essentially
small at the universe of that site: it is equivalent to the slice `(Sch/S)/X`, which is
essentially small because the underlying category of schemes is (Stacks 000J). This is what makes
the morphism of ringed topoi of Stacks 06TW available for `𝒳` itself, and not only for the
slice. -/
theorem essentiallySmall_of_representableBy : EssentiallySmall.{u} 𝒳 :=
  (essentiallySmall_congr e.toEquivalence).2 inferInstance

omit [EssentiallySmall.{u} B.Schemes] in
/-- The inverse-image form of the structure map of the morphism of ringed topoi of Stacks 06TW is
a *transport* in the sense of `Stacks.IsTransport`: it is the identification
`AlgebraicGeometry.Stack.structureSheafInverseImageIso` of the structure sheaves
(`AlgebraicGeometry.Stack.fSharpInverseImage_associatedRingedToposHom`), which is the canonical
comparison of the inverse image of a sheaf of commutative rings with restriction followed by the
equality `AlgebraicGeometry.Stack.sheafPushforwardContinuous_structureSheaf`; the first is the
identity on underlying sheaves of sets, so on sheaves of sets only `eqToHom` of that equality
remains. -/
theorem isTransport_fSharpInverseImageForget_associatedRingedToposHom
    [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴] (hFib : p.IsFibredOneMorphism q F) :
    Stacks.IsTransport
      (associatedRingedToposHom B S hS p q F hp hq τ hτ hFib).fSharpInverseImageForget := by
  have := isContinuous_associatedTopology_of_comp_eq B S hS τ hp hq hFib.comp_eq
  have h := RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (X := associatedRingedTopos B S hS p hp τ hτ)
    (Y := associatedRingedTopos B S hS q hq τ hτ)
    (associatedRingedToposHom B S hS p q F hp hq τ hτ hFib)
  have key : (associatedRingedTopos B S hS p hp τ hτ).forgetRing.map
        (associatedRingedToposHom B S hS p q F hp hq τ hτ hFib).fSharpInverseImage =
      (associatedRingedTopos B S hS p hp τ hτ).forgetRing.map
        (eqToHom (sheafPushforwardContinuous_structureSheaf B S hS p q F hp hq τ hτ
          hFib.comp_eq)) := by
    rw [fSharpInverseImage_associatedRingedToposHom]
    rfl
  rw [← h, key]
  exact (Stacks.IsTransport.eqToHom _).map _

/-- **Stacks 075J.** The morphism of ringed topoi
`(Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)` of the morphism of schemes `g : X ⟶ Y` over `S`
corresponding to `F`: the morphism of ringed topoi of Stacks 06TW of the 1-morphism
`CategoryTheory.Over.map g` of slices. -/
@[stacks 075J "the morphism of ringed topoi of the morphism of schemes"]
noncomputable def representingObjectRingedToposHom (hF : F ⋙ q = p) :
    RingedToposHom (associatedRingedTopos B S hS (Over.forget X) (.over_forget X) τ hτ)
      (associatedRingedTopos B S hS (Over.forget Y) (.over_forget Y) τ hτ) :=
  associatedRingedToposHom B S hS (Over.forget X) (Over.forget Y)
    (Over.map (representingObjectHom B S hS p q F X Y e d hF)) (.over_forget X) (.over_forget Y)
    τ hτ ((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism
      (Over.mapForget_eq (representingObjectHom B S hS p q F X Y e d hF)))

/-- The structure map of the morphism of ringed topoi of the corresponding morphism of schemes is
a transport, this being the case `F := Over.map g` of
`AlgebraicGeometry.Stack.isTransport_fSharpInverseImageForget_associatedRingedToposHom`. -/
theorem isTransport_fSharpInverseImageForget_representingObjectRingedToposHom
    (hF : F ⋙ q = p) :
    Stacks.IsTransport
      (representingObjectRingedToposHom B S hS p q F X Y e d τ hτ hF).fSharpInverseImageForget :=
  isTransport_fSharpInverseImageForget_associatedRingedToposHom B S hS (Over.forget X)
    (Over.forget Y) _ (.over_forget X) (.over_forget Y) τ hτ _

section Conjugate

variable [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]

/-- **Stacks 075J.** The morphism of ringed topoi `F : (Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴)` of
Stacks 06TW, read through the two representing equivalences of Stacks 075I: the composite
`(Sh((Sch/X)_τ), O_X) → (Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴) → (Sh((Sch/Y)_τ), O_Y)` of morphisms of
ringed topoi, whose outer two factors are the morphisms of ringed topoi of the 1-morphisms `e⁻¹`
and `d` of the two representing equivalences. -/
@[stacks 075J "the morphism of ringed topoi of the 1-morphism, read on the representing sites"]
noncomputable def conjugatedRingedToposHom (hF : F ⋙ q = p) :
    RingedToposHom (associatedRingedTopos B S hS (Over.forget X) (.over_forget X) τ hτ)
      (associatedRingedTopos B S hS (Over.forget Y) (.over_forget Y) τ hτ) :=
  RingedToposHom.comp
    (X := associatedRingedTopos B S hS (Over.forget X) (.over_forget X) τ hτ)
    (Y := associatedRingedTopos B S hS q hq τ hτ)
    (Z := associatedRingedTopos B S hS (Over.forget Y) (.over_forget Y) τ hτ)
    (associatedRingedToposHom B S hS q (Over.forget Y) d.hom.functor hq (.over_forget Y) τ hτ
      ((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism d.hom.w))
    (RingedToposHom.comp
      (X := associatedRingedTopos B S hS (Over.forget X) (.over_forget X) τ hτ)
      (Y := associatedRingedTopos B S hS p hp τ hτ)
      (Z := associatedRingedTopos B S hS q hq τ hτ)
      (associatedRingedToposHom B S hS p q F hp hq τ hτ (hq.isFibredOneMorphism hF))
      (associatedRingedToposHom B S hS (Over.forget X) p e.inv.functor (.over_forget X) hp τ hτ
        (hp.isFibredOneMorphism e.inv.w)))

/-- The comparison of the inverse images of the two morphisms of ringed topoi of Stacks 075J:
both are restriction of sheaves, along `e⁻¹ ⋙ F ⋙ d` and along `Over.map g` respectively, and
those two 1-morphisms of slices are equal
(`AlgebraicGeometry.Stack.eq_map_representingObjectHom`), so the comparison is the canonical one
attached to that equality. -/
noncomputable def conjugatedRingedToposHomInverseImageIso (hF : F ⋙ q = p) :
    (conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ hτ hF).toToposHom.inverseImage ≅
      (representingObjectRingedToposHom B S hS p q F X Y e d τ hτ
        hF).toToposHom.inverseImage := by
  haveI : p.IsFibered := hp.isFibered
  haveI : q.IsFibered := hq.isFibered
  haveI : (Over.forget X).IsFibered := (Functor.IsFiberedInGroupoids.over_forget X).isFibered
  haveI : (Over.forget Y).IsFibered := (Functor.IsFiberedInGroupoids.over_forget Y).isFibered
  haveI := ((hp.isFibredOneMorphism e.inv.w).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  haveI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  haveI := (((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism
    d.hom.w).isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  haveI := (((Functor.IsFiberedInGroupoids.over_forget Y).isFibredOneMorphism
    (Over.mapForget_eq (representingObjectHom B S hS p q F X Y e d
      hF))).isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  haveI := Functor.isContinuous_comp F d.hom.functor (associatedTopology B S hS p τ)
    (associatedTopology B S hS q τ) (associatedTopology B S hS (Over.forget Y) τ)
  exact Functor.sheafPushforwardContinuousComp'
    (eqToIso (eq_map_representingObjectHom B S hS p q F X Y e d hF)) (Type u)
    (associatedTopology B S hS (Over.forget X) τ) (associatedTopology B S hS p τ)
    (associatedTopology B S hS (Over.forget Y) τ)

/-- The comparison of the two inverse images is a transport: restriction along `e⁻¹` and then
along `F ⋙ d` *is* restriction along the composite, and the composite is `Over.map g` on the
nose. -/
theorem isTransport_conjugatedRingedToposHomInverseImageIso_hom (hF : F ⋙ q = p) :
    Stacks.IsTransport
      (conjugatedRingedToposHomInverseImageIso B S hS p q F X Y e d hp hq τ hτ hF).hom := by
  have := isContinuous_associatedTopology_of_comp_eq B S hS τ (.over_forget X) hp e.inv.w
  have := isContinuous_associatedTopology_of_comp_eq B S hS τ hp hq hF
  have := isContinuous_associatedTopology_of_comp_eq B S hS τ hq (.over_forget Y) d.hom.w
  have := isContinuous_associatedTopology_of_comp_eq B S hS τ (.over_forget X) (.over_forget Y)
    (Over.mapForget_eq (representingObjectHom B S hS p q F X Y e d hF))
  have := Functor.isContinuous_comp F d.hom.functor (associatedTopology B S hS p τ)
    (associatedTopology B S hS q τ) (associatedTopology B S hS (Over.forget Y) τ)
  exact Functor.isTransport_sheafPushforwardContinuousComp'_hom
    (eq_map_representingObjectHom B S hS p q F X Y e d hF) (Type u)
    (associatedTopology B S hS (Over.forget X) τ) (associatedTopology B S hS p τ)
    (associatedTopology B S hS (Over.forget Y) τ)

/-- The structure map of the composite of the three morphisms of ringed topoi is a transport,
each of the three being one. -/
theorem isTransport_fSharpInverseImageForget_conjugatedRingedToposHom (hF : F ⋙ q = p) :
    Stacks.IsTransport
      (conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ hτ hF).fSharpInverseImageForget := by
  apply RingedToposHom.isTransport_fSharpInverseImageForget_comp
  · exact isTransport_fSharpInverseImageForget_associatedRingedToposHom B S hS q (Over.forget Y)
      d.hom.functor hq (.over_forget Y) τ hτ _
  · apply RingedToposHom.isTransport_fSharpInverseImageForget_comp
    · exact isTransport_fSharpInverseImageForget_associatedRingedToposHom B S hS p q F hp hq τ hτ _
    · exact isTransport_fSharpInverseImageForget_associatedRingedToposHom B S hS (Over.forget X) p
        e.inv.functor (.over_forget X) hp τ hτ _

end Conjugate

/-- **Stacks 075J.** The two morphisms of ringed topoi agree. The morphism of ringed topoi
`F : (Sh(𝒳_τ), O_𝒳) → (Sh(𝒴_τ), O_𝒴)` of Stacks 06TW, read through the two representing
equivalences of Stacks 075I, and the morphism of ringed topoi
`g : (Sh((Sch/X)_τ), O_X) → (Sh((Sch/Y)_τ), O_Y)` of the corresponding morphism of schemes have
the same inverse image up to the canonical comparison
`AlgebraicGeometry.Stack.conjugatedRingedToposHomInverseImageIso`, and under that comparison
their structure maps `g⁻¹O_Y ⟶ O_X` coincide as morphisms of sheaves of *commutative rings*: the
comparison of the two inverse images of the structure sheaf of `(Sch/S)/Y` takes the one to the
other. -/
@[stacks 075J "the two morphisms of ringed topoi agree, structure sheaves included"]
theorem fSharpInverseImage_conjugatedRingedToposHom (hF : F ⋙ q = p) :
    haveI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_representableBy B S hS p X e
    haveI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_representableBy B S hS q Y d
    (conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ hτ hF).fSharpInverseImage =
      (pullbackCommRingSheafIsoOfNatIso (associatedTopology B S hS (Over.forget X) τ)
          (conjugatedRingedToposHomInverseImageIso B S hS p q F X Y e d hp hq τ hτ hF)
          (structureSheaf B S hS (Over.forget Y)
            (Functor.IsFiberedInGroupoids.over_forget Y) τ hτ)).hom ≫
        (representingObjectRingedToposHom B S hS p q F X Y e d τ hτ hF).fSharpInverseImage :=
  have : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_representableBy B S hS p X e
  have : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_representableBy B S hS q Y d
  RingedToposHom.fSharpInverseImage_eq_of_isTransport _ _
    (conjugatedRingedToposHomInverseImageIso B S hS p q F X Y e d hp hq τ hτ hF)
    (isTransport_fSharpInverseImageForget_conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ
      hτ hF)
    (isTransport_fSharpInverseImageForget_representingObjectRingedToposHom B S hS p q F X Y e d τ
      hτ hF)
    (isTransport_conjugatedRingedToposHomInverseImageIso_hom B S hS p q F X Y e d hp hq τ hτ hF)

/-- **Stacks 075J.** The square of morphisms of ringed topoi commutes, in the direct-image form
in which a morphism of ringed topoi (Stacks 01D3) states its structure map: the structure map of
`F` read through the two representing equivalences of Stacks 075I, transported along the adjoint
mate of the comparison of the two inverse images, is the structure map of the morphism of ringed
topoi of the corresponding morphism of schemes. -/
@[stacks 075J "the square of morphisms of ringed topoi commutes"]
theorem fSharp_conjugatedRingedToposHom (hF : F ⋙ q = p) :
    haveI : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_representableBy B S hS p X e
    haveI : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_representableBy B S hS q Y d
    (associatedRingedTopos B S hS (Over.forget Y) (.over_forget Y) τ hτ).forgetRing.map
          (conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ hτ hF).fSharp ≫
        (((conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ hτ
              hF).toToposHom.adj.ofNatIsoLeft
            (conjugatedRingedToposHomInverseImageIso B S hS p q F X Y e d hp hq τ hτ
              hF)).rightAdjointUniq
          (representingObjectRingedToposHom B S hS p q F X Y e d τ hτ
            hF).toToposHom.adj).hom.app
          ((associatedRingedTopos B S hS (Over.forget X) (.over_forget X) τ hτ).forgetRing.obj
            (structureSheaf B S hS (Over.forget X)
              (Functor.IsFiberedInGroupoids.over_forget X) τ hτ)) =
      (associatedRingedTopos B S hS (Over.forget Y) (.over_forget Y) τ hτ).forgetRing.map
        (representingObjectRingedToposHom B S hS p q F X Y e d τ hτ hF).fSharp :=
  have : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_representableBy B S hS p X e
  have : EssentiallySmall.{u} 𝒴 := essentiallySmall_of_representableBy B S hS q Y d
  RingedToposHom.ringedSquare_of_isTransport _ _
    (conjugatedRingedToposHomInverseImageIso B S hS p q F X Y e d hp hq τ hτ hF)
    (isTransport_fSharpInverseImageForget_conjugatedRingedToposHom B S hS p q F X Y e d hp hq τ
      hτ hF)
    (isTransport_fSharpInverseImageForget_representingObjectRingedToposHom B S hS p q F X Y e d τ
      hτ hF)
    (isTransport_conjugatedRingedToposHomInverseImageIso_hom B S hS p q F X Y e d hp hq τ hτ hF)

end RingedTopoi

end AlgebraicGeometry.Stack

end
