module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClassUnit
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalThroughBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.EmbeddedPointCounterexample
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionProductDedekind
public import StacksCore.Tactic.StacksAttribute

/-!
# Bivariant classes of smooth morphisms, and the Chow cohomology of smooth schemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The following results
follow from the Gysin class `Δ^!` of the diagonal of a smooth morphism
(`Stacks.Chow.diagonalGysinClass`, Stacks 0FBR) and its two properties: it commutes with every
bivariant class (Stacks 0FBP, `Stacks.Chow.diagonalGysinClass_bivariantCommute`) and
`Δ^! ∘ pr_i^* = 1` (Stacks 0FBS).

* **Stacks 0FBT.** For `g : Y ⟶ Z` smooth of relative dimension `d` and `f : X ⟶ Y`,
  `c ↦ c ∘ g^*` is an isomorphism `A^p(X ⟶ Y) ≃ A^{p-d}(X ⟶ Z)`
  (`Stacks.Chow.smoothRelativeDimensionShiftEquiv`).
* **Stacks 0FC2.** For `X` smooth over a field `k`, equidimensional of dimension `d`, the map
  `A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`, is bijective
  (`Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_smooth_field`), and it carries
  composition to the intersection product
  (`Stacks.Chow.chowCohomologyCapFundamentalClass_mulId_of_smooth_field`).
* **Stacks 0FCB, over a base of pure dimension one.** The same over a base as in section 42.63
  with no zero-dimensional component, with `[X]_d` for `d = e + 1`, where `e` is the relative
  dimension of `X` over `S`
  (`Stacks.Chow.IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_of_smooth`,
  `Stacks.Chow.IsDedekindChowBase.chowCohomologyCapFundamentalClass_mulId_of_smooth`). Stacks
  0FCB itself allows field components in the base.

## Implementation notes

"Equidimensional of dimension `d`" is carried as "of constant relative dimension `d`" over the
field, and "of constant relative dimension `e`" over the Dedekind base with `d = e + 1`. For a
smooth scheme over a field the two readings agree. Over a base of section 42.63 without
zero-dimensional components, a smooth scheme of relative dimension `e` is equidimensional of
dimension `e + 1`.

The intersection products are those of Stacks 0FC0 (`Stacks.Chow.intersectionProduct`) and of
section 42.64 (`Stacks.Chow.IsDedekindChowBase.intersectionProduct`), each formed with
`Δ^! = Stacks.Chow.diagonalGysinClass`. Over the Dedekind base the two results assume
`Stacks.Chow.HasNoZeroDimensionalComponent`, under which Stacks 0FC5 holds on all of `S`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Chow

/-! ### Stacks 0FBT -/

section Shift

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [Smooth g]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (d : ℕ) (hgd : AlgebraicGeometry.RelativeDimension g d)
  (p : ℤ)

/-- **Stacks 0FBT.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes locally of finite
type over `S`, with `g` smooth of relative dimension `d`. Then `c ↦ c ∘ g^*` is an isomorphism

  `A^p(X ⟶ Y) ≃ A^{p-d}(X ⟶ Z)`,

with inverse `c' ↦ res(Δ^!) ∘ res(c')`, where `Δ^!` is the Gysin class of the diagonal of `g`
(Stacks 0FBR). For a smooth `g` the Gysin map `g^!` of Stacks 0FEZ is the flat pullback `g^*`. -/
@[stacks 0FBT "g^! read as the flat pullback g^* of the smooth morphism g; bivariant classes are \
those of the Gysin system of invertible modules, `Stacks.Chow.gysinSystemOfInvertible`"]
def smoothRelativeDimensionShiftEquiv :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p ≃+
      BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
        (comp_comp_structureMorphism_eq hf hg) (p - d) :=
  smoothShiftEquiv C sX sY sZ f g hf hg d hgd p (diagonalGysinClass C sY g hgd)
    (diagonalGysinClass_bivariantCommute C sY g hgd)
    (diagonalGysinClass_compFlatPullbackEqOne_fst C sY g hgd)
    (diagonalGysinClass_compFlatPullbackEqOne_snd C sY g hgd sZ hg)

/-- The equivalence `smoothRelativeDimensionShiftEquiv` sends `c` to `c ∘ g^*`. -/
@[simp]
theorem smoothRelativeDimensionShiftEquiv_apply
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :
    smoothRelativeDimensionShiftEquiv C sX sY sZ f g hf hg d hgd p c =
      smoothShiftForward C sX sY sZ f g hf hg d hgd p c :=
  rfl

/-- The map `c ↦ c ∘ g^*` of Stacks 0FBT is bijective. -/
theorem smoothShiftForward_bijective :
    Function.Bijective (smoothShiftForward C sX sY sZ f g hf hg d hgd p) :=
  (smoothRelativeDimensionShiftEquiv C sX sY sZ f g hf hg d hgd p).bijective

end Shift

/-! ### Stacks 0FC2 and Stacks 0FCB: bijectivity -/

section CongrHom

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f f' : X ⟶ Y}
  [LocallyOfFiniteType f] [LocallyOfFiniteType f'] {hf : f ≫ sY = sX} {p : ℤ}

/-- Reading a class for an equal morphism is bijective. -/
theorem congrHomAddHom_bijective (e : f = f') (hf' : f' ≫ sY = sX) :
    Function.Bijective (congrHomAddHom (C := C) (G := G) (hf := hf) (p := p) e hf') := by
  subst e
  exact Function.bijective_id

end CongrHom

section Bijective

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [Smooth sX] (e : ℕ) (he : AlgebraicGeometry.RelativeDimension sX e) (p : ℤ)

/-- For `X` smooth of relative dimension `e` over the base, `c ↦ c ∘ g^*`,
`A^p(X) ⟶ A^{p-e}(X ⟶ S)`, is bijective (Stacks 0FBT for `g : X ⟶ S`). -/
theorem compStructureFlatPullbackClass_bijective :
    Function.Bijective (compStructureFlatPullbackClass C sX e he p) :=
  (congrHomAddHom_bijective (Category.id_comp sX) (Category.comp_id sX)).comp
    (smoothShiftForward_bijective C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
      (Category.comp_id sX) e he p)

end Bijective

/-! ### Stacks 0FC2 -/

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [Smooth sX] (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension sX d)

include hd in
/-- **Stacks 0FC2, first clause.** Let `X` be smooth over a field `k`, of constant relative
dimension `d`, that is equidimensional of dimension `d`. Then

  `A^p(X) ⟶ CH_{d-p}(X)`,  `c ↦ c ∩ [X]_d`

is bijective. -/
@[stacks 0FC2 "first clause; equidimensional of dimension d read as of constant relative \
dimension d over k; bivariant classes are those of the Gysin system of invertible modules"]
theorem chowCohomologyCapFundamentalClass_bijective_of_smooth_field (p : ℤ) :
    Function.Bijective (chowCohomologyCapFundamentalClass (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX d p) :=
  chowCohomologyCapFundamentalClass_bijective_of_bivariantToBaseEval _ sX d hd p
    (schemeDeltaDimension_le_zero_fieldChowSituation k (𝟙 _))
    (compStructureFlatPullbackClass_bijective _ sX d hd p)
    (bivariantToBaseEval_bijective_of_field sX _)

/-- **Stacks 0FC2, second clause.** Let `X` be smooth over a field `k`, of constant relative
dimension `d`. Via `Θ : A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`, composition of bivariant classes
becomes the intersection product of Stacks 0FC0 formed with the Gysin class `Δ^!` of the
diagonal (Stacks 0FBR):

  `Θ(a · b) = Θ(a) · Θ(b)`. -/
@[stacks 0FC2 "second clause, with the intersection product of Stacks 0FC0 formed with the \
Gysin class Δ^! of the diagonal; equidimensional of dimension d read as of constant relative \
dimension d over k"]
theorem chowCohomologyCapFundamentalClass_mulId_of_smooth_field (p q : ℤ)
    (a : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX p)
    (b : chowCohomologyComponent (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX q) :
    chowCohomologyCapFundamentalClass (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX d (p + q)
        (a.mulId (fieldChowSituation k) sX b) =
      chowGroupDegreeEquiv (fieldChowSituation k) sX
        (by ring : ((d : ℤ) - p) + (d - q) - d = d - (p + q))
        (chowGroupSelfProductUnitCollapse (fieldChowSituation k) sX
          (((d : ℤ) - p) + (d - q) - d)
          (intersectionProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (gysinSystemOfInvertible (fieldChowSituation k)) sX (𝟙 X) (𝟙 X) d
            (bivariantClassCongrBase (fieldChowSituation k)
              (gysinSystemOfInvertible (fieldChowSituation k)) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure (fieldChowSituation k) sX) rfl d
              (diagonalGysinClass (fieldChowSituation k) sX sX hd))
            ((d : ℤ) - p) ((d : ℤ) - q)
            (chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - p)
              (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                (gysinSystemOfInvertible (fieldChowSituation k)) sX d p a) ⊗ₜ[ℤ]
              chowGroupCongr (fieldChowSituation k) (Category.id_comp sX).symm ((d : ℤ) - q)
                (chowCohomologyCapFundamentalClass (fieldChowSituation k)
                  (gysinSystemOfInvertible (fieldChowSituation k)) sX d q b)))) :=
  chowCohomologyCapFundamentalClass_mulId k sX d hd _
    (diagonalGysinClass_bivariantCommute _ sX sX hd)
    (diagonalGysinClass_compFlatPullbackEqOne_snd _ sX sX hd (𝟙 _) (Category.comp_id sX)) p q a b

end Field

/-! ### Stacks 0FCB over a base of pure dimension one -/

namespace IsDedekindChowBase

section Dedekind

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) (hS1 : HasNoZeroDimensionalComponent C)
  {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Smooth sX] (e : ℕ)
  (he : AlgebraicGeometry.RelativeDimension sX e)

include hS hS1 he in
/-- **The first clause of Stacks 0FCB over a base of pure dimension one.** Let `S` be a base as in
section 42.63 with no zero-dimensional component, and let `X` be smooth over `S` of constant
relative dimension `e`. Then

  `A^p(X) ⟶ CH_{(e+1)-p}(X)`,  `c ↦ c ∩ [X]_{e+1}`

is bijective. -/
theorem chowCohomologyCapFundamentalClass_bijective_of_smooth (p : ℤ) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p) :=
  chowCohomologyCapFundamentalClass_bijective_of_bivariantCapBaseFundamentalClass C sX e he p
    (hS.schemeDeltaDimension_le_one _)
    (compStructureFlatPullbackClass_bijective C sX e he p)
    (bivariantCapBaseFundamentalClass_bijective C sX _ hS hS1)

include hS1 in
/-- **The second clause of Stacks 0FCB over a base of pure dimension one.** Let `S` be a base as
in section 42.63 with no zero-dimensional component, and let `X` be smooth over `S` of constant
relative dimension `e`. Via `Θ : A^p(X) ⟶ CH_{(e+1)-p}(X)`, `c ↦ c ∩ [X]_{e+1}`, composition of
bivariant classes becomes the intersection product of section 42.64 formed with the Gysin class
`Δ^!` of the diagonal (Stacks 0FBR):

  `Θ(a · b) = Θ(a) · Θ(b)`. -/
theorem chowCohomologyCapFundamentalClass_mulId_of_smooth (p q : ℤ)
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) :
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) (p + q)
        (a.mulId C sX b) =
      chowGroupDegreeEquiv C sX
        (by ring : ((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e = (e + 1) - (p + q))
        (chowGroupSelfProductUnitCollapse C sX (((e : ℤ) + 1 - p) + ((e : ℤ) + 1 - q) - 1 - e)
          (hS.intersectionProduct (gysinSystemOfInvertible C) sX (𝟙 X) (𝟙 X) e
            (bivariantClassCongrBase C (gysinSystemOfInvertible C) (pullback.diagonal sX)
              (diagonal_comp_selfProductStructure C sX) rfl e (diagonalGysinClass C sX sX he))
            ((e : ℤ) + 1 - p) ((e : ℤ) + 1 - q)
            (chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - p)
              (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) p a)
              ⊗ₜ[ℤ] chowGroupCongr C (Category.id_comp sX).symm ((e : ℤ) + 1 - q)
                (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX (e + 1) q
                  b)))) :=
  hS.chowCohomologyCapFundamentalClass_mulId sX e he _
    (diagonalGysinClass_bivariantCommute C sX sX he)
    (diagonalGysinClass_compFlatPullbackEqOne_snd C sX sX he (𝟙 C.S) (Category.comp_id sX)) p q
    (fun c' ↦ isExteriorProductOverBase_bivariantCapBaseFundamentalClass sX _ hS hS1 c') a b

end Dedekind

end IsDedekindChowBase

end Stacks.Chow

end
