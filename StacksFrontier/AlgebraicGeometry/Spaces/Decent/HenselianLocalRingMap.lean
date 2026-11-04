module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FlatHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.RingTheory.Henselian.Canonicity

/-!
# The map of henselian local rings induced by a morphism of decent algebraic spaces

Let `f : X ⟶ Y` be a morphism of decent algebraic spaces over `S`, let `x` be a point of `X`
and let `y = f(x)`. There is a local homomorphism

  `φ : 𝒪^h_{Y, y} ⟶ 𝒪^h_{X, x}`

of the henselian local rings at those two points, and it is flat as soon as `f` is flat.

The construction is the universal property of the henselization. Choose an elementary étale
neighborhood `V` of `y` in `Y`; by
`AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_pullback_isLocalHom` the point `x`
has an elementary étale neighborhood `U` in `X` admitting a morphism of schemes
`j : U ⟶ V` over `f` carrying the distinguished point to the distinguished point, so that the
stalks at those points are related by a local homomorphism `α : 𝒪_{V, v} ⟶ 𝒪_{U, u}`. Now
`𝒪^h_{X, x}` is henselian local and `𝒪^h_{Y, y}` is a henselization of `𝒪_{V, v}`
(`AlgebraicGeometry.Space.henselianLocalRing_isHenselization`), so the composite
`𝒪_{V, v} ⟶ 𝒪_{U, u} ⟶ 𝒪^h_{X, x}` extends uniquely to a local homomorphism out of
`𝒪^h_{Y, y}`, by Stacks 04GS in the form
`HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale`.

Flatness is read off the same square. The commuting square of étale charts
`U ⟶ V` over `f` is one of the squares tested by `AlgebraicGeometry.Space.IsFlat`, so `j` is a
flat morphism of schemes and `α` is a flat homomorphism; `𝒪^h_{X, x}` is flat over `𝒪_{U, u}`
because a henselization is flat, hence flat over `𝒪_{V, v}`; and flatness over a local ring
ascends to its henselization, which is `Module.Flat.of_isHenselization`.

## Main results

* `AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare`: the homomorphism of
  henselian local rings induced by a morphism of decent algebraic spaces at a point, together
  with the commuting square of pointed étale charts that exhibits it as induced — the
  homomorphism agrees with the stalk map of that square on the images of the stalk of the chart
  of `Y` — and with its locality and its flatness when the morphism is flat.
* `AlgebraicGeometry.Space.exists_henselianLocalRingHom`: the same with the square forgotten,
  which is the form the consumers take as a hypothesis.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_genericHenselianLocalRingHom`: the same at the
  generic point of a prime divisor of `X` lying over the generic point of a prime divisor of
  `Y`, which is the shape in which the flat pullback of cycles uses it.

## Implementation notes

The homomorphism is produced existentially rather than as a named definition. Both inputs it is
built from are themselves existential — the elementary étale neighborhood of `y` supplied by
decency of `Y` and the neighborhood of `x` over it supplied by
`exists_elementaryEtaleNeighborhood_pullback` — and neither comes with a canonical choice in
this development, so nothing would be pinned by naming the result of one choice. What is pinned
is the relation to `f`, and it is carried in the statement: the chart square and the
compatibility of the homomorphism with its stalk map are part of
`exists_henselianLocalRingHom_chartSquare`, and the universal property makes the homomorphism
the *only* local one with that compatibility, since a local homomorphism out of `𝒪^h_{Y, y}`
agreeing with a given one on the image of `𝒪_{V, v}` is unique
(`HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale`). Independence of the choice of
square is not asserted; it would need the cofilteredness of the squares over `f`, which this
development does not have.

Flatness of `f` appears as a hypothesis of the conclusion rather than of the statement, so that
the one homomorphism obtained is simultaneously local and, in the flat case, flat; the two
properties are needed together by the consumers.

Both henselian local rings are local rings by
`AlgebraicGeometry.Space.henselianLocalRing_isLocalRing`, which needs decency of the space in
question; decency of `X` is used a second time, for the elementary étale neighborhood of `x`
over `V`.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chart `U ⟶ X` of an elementary étale neighborhood is an étale chart in the sense of
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`. -/
private theorem presheaf_etale_neighborhood_toSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf U.toSpace := by
  simpa using U.etale_toSpace U.scheme (𝟙 _) (presheaf_etale_id B S hS U.scheme)

/-- **The map of henselian local rings induced by a morphism of decent algebraic spaces.** Let
`f : X ⟶ Y` be a morphism of decent algebraic spaces over `S` and let `x` be a point of `X`.
There is a commuting square of pointed étale charts — an elementary étale neighborhood `V` of
`f(x)` in `Y`, an elementary étale neighborhood `U` of `x` in `X` and a morphism of schemes
`j : U ⟶ V` over `f` carrying the distinguished point to the distinguished point — and a local
ring homomorphism `φ : 𝒪^h_{Y, f(x)} ⟶ 𝒪^h_{X, x}` which agrees on the image of `𝒪_{V, v}`
with the stalk map of that square. It is flat when `f` is flat.

`φ` is obtained from the universal property of the henselization, Stacks 04GS: the square gives
a local homomorphism `𝒪_{V, v} ⟶ 𝒪_{U, u}` of the stalks, hence a local homomorphism of
`𝒪_{V, v}` into the henselian local ring `𝒪^h_{X, x}`, and `𝒪^h_{Y, f(x)}` is a henselization
of `𝒪_{V, v}`; the stated compatibility is exactly that `φ` extends it, and it determines `φ`
among local homomorphisms. When `f` is flat the morphism `j` is flat, so `𝒪^h_{X, x}` is flat
over `𝒪_{V, v}`, and flatness ascends to the henselization. -/
theorem exists_henselianLocalRingHom_chartSquare
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYd : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    ∃ (V : ElementaryEtaleNeighborhood B S hS Y hY (pointsMap B S hS X f x))
      (U : ElementaryEtaleNeighborhood B S hS X hX x) (j : U.scheme ⟶ V.scheme)
      (hj : j.left.1 U.point = V.point)
      (φ : (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) →+*
        (henselianLocalRing B S hS X hX x hXd : Type (u + 1))),
      yoneda.map j ≫ V.toSpace = U.toSpace ≫ f ∧
        IsLocalHom φ ∧
        (∀ a, φ (stalkToHenselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd V a) =
          stalkToHenselianLocalRing B S hS X hX x hXd U
            (((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
              j.left.1.stalkMap U.point).hom a)) ∧
        (IsFlat B S hS f → φ.Flat) := by
  classical
  obtain ⟨V, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hY hYd
    (pointsMap B S hS X f x)
  obtain ⟨U, j, hj, hsq, hloc⟩ :=
    exists_elementaryEtaleNeighborhood_pullback_isLocalHom B S hS hY hX hXd f x V
  set α : V.scheme.left.1.presheaf.stalk V.point →+*
      U.scheme.left.1.presheaf.stalk U.point :=
    ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap U.point).hom with hαdef
  let : IsLocalRing (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd :
      Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd
  let : IsLocalRing (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX x hXd
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) :=
    stalkAlgebra B S hS Y hY (pointsMap B S hS X f x) hYd V
  let : Algebra (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    stalkAlgebra B S hS X hX x hXd U
  let : IsHenselization (V.scheme.left.1.presheaf.stalk V.point)
      (ResidueField (V.scheme.left.1.presheaf.stalk V.point))
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS Y hY (pointsMap B S hS X f x) hYd V
  let : IsHenselization (U.scheme.left.1.presheaf.stalk U.point)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS X hX x hXd U
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point) := α.toAlgebra
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    ((stalkToHenselianLocalRing B S hS X hX x hXd U).comp α).toAlgebra
  have : IsScalarTower (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalHom α := hloc
  have : IsLocalHom (stalkToHenselianLocalRing B S hS X hX x hXd U) :=
    isLocalHom_stalkToHenselianLocalRing B S hS X hX x hXd U
  have : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))) :=
    isLocalHom_stalkToHenselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd V
  have : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1))) :=
    RingHom.isLocalHom_comp _ _
  have : HenselianLocalRing (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsHenselization.henselian (U.scheme.left.1.presheaf.stalk U.point)
      (ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  obtain ⟨g, hg, -⟩ := HenselianLocalRing.existsUnique_isLocalHom_of_ind_etale
    (R := V.scheme.left.1.presheaf.stalk V.point)
    (Rh := (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)))
    (Sh := (henselianLocalRing B S hS X hX x hXd : Type (u + 1)))
    (IsHenselization.ind_etale
      (R := V.scheme.left.1.presheaf.stalk V.point)
      (L := ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
    (IsHenselization.residueField_map_bijective
      (R := V.scheme.left.1.presheaf.stalk V.point)).surjective
  refine ⟨V, U, j, hj, (g : _ →+* _), hsq, ⟨fun a ha ↦ hg.map_nonunit a ha⟩,
    fun a ↦ g.commutes a, fun hf ↦ ?_⟩
  have : AlgebraicGeometry.Flat j.left.1 :=
    hf U.scheme V.scheme U.toSpace V.toSpace j
      (presheaf_etale_neighborhood_toSpace B S hS hX x U)
      (presheaf_etale_neighborhood_toSpace B S hS hY (pointsMap B S hS X f x) V) hsq
  have : Module.Flat (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point) := by
    have hαflat : α.Flat := by
      rw [hαdef, CommRingCat.hom_comp]
      exact RingHom.Flat.comp
        (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
        (AlgebraicGeometry.Flat.stalkMap j.left.1 U.point)
    exact hαflat
  have : Module.Flat (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsHenselization.flat (L := ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  have : Module.Flat (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    Module.Flat.trans (V.scheme.left.1.presheaf.stalk V.point)
      (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1))
  let : Algebra (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    (g : _ →+* _).toAlgebra
  have : IsScalarTower (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1))
      (henselianLocalRing B S hS X hX x hXd : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (g.commutes a).symm
  exact Module.Flat.of_isHenselization
    (R := V.scheme.left.1.presheaf.stalk V.point)
    (Rh := (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)))
    (ResidueField (V.scheme.left.1.presheaf.stalk V.point))
    (henselianLocalRing B S hS X hX x hXd : Type (u + 1))

/-- **The map of henselian local rings induced by a morphism of decent algebraic spaces**, with
the commuting square of charts that produces it forgotten. Let `f : X ⟶ Y` be a morphism of
decent algebraic spaces over `S` and let `x` be a point of `X`. There is a local ring
homomorphism `𝒪^h_{Y, f(x)} ⟶ 𝒪^h_{X, x}`, flat when `f` is flat.

`AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare` is the same statement with
the compatibility that identifies the homomorphism as the one `f` induces. -/
theorem exists_henselianLocalRingHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYd : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    ∃ φ : (henselianLocalRing B S hS Y hY (pointsMap B S hS X f x) hYd : Type (u + 1)) →+*
        (henselianLocalRing B S hS X hX x hXd : Type (u + 1)),
      IsLocalHom φ ∧ (IsFlat B S hS f → φ.Flat) :=
  let ⟨_, _, _, _, φ, _, hloc, _, hflat⟩ :=
    exists_henselianLocalRingHom_chartSquare B S hS hX hXd hY hYd f x
  ⟨φ, hloc, hflat⟩

/-- **The map of henselian local rings at the generic points of prime divisors.** Let
`f : X ⟶ Y` be a flat morphism of decent algebraic spaces over `S`, let `Z ⊆ X` and `Z' ⊆ Y` be
prime divisors with generic points `ξ` and `ξ'`, and suppose `ξ` lies over `ξ'`. There is a flat
local homomorphism `𝒪^h_{Y, ξ'} ⟶ 𝒪^h_{X, ξ}`.

This is `AlgebraicGeometry.Space.exists_henselianLocalRingHom` at the generic point of `Z`. -/
theorem PrimeDivisor.exists_genericHenselianLocalRingHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXd : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYd : IsDecentSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (ZX : PrimeDivisor B S hS X) (ZY : PrimeDivisor B S hS Y)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y) :
    ∃ φ : ↥(ZY.genericHenselianLocalRing B S hS hY hYd) →+*
        ↥(ZX.genericHenselianLocalRing B S hS hX hXd),
      IsLocalHom φ ∧ φ.Flat := by
  have key := exists_henselianLocalRingHom B S hS hX hXd hY hYd f
    (ZX.genericPoint B S hS X)
  rw [hZ] at key
  obtain ⟨φ, hφloc, hφflat⟩ := key
  exact ⟨φ, hφloc, hφflat hf⟩

end AlgebraicGeometry.Space

end
