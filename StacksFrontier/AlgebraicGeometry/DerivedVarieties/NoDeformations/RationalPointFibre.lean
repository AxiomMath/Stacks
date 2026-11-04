module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ConstantFamily
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The fibre over a `k`-rational point is the scheme-theoretic fibre

Let `k` be a field, let `q : S ⟶ Spec k` be a morphism with a section `s : Spec k ⟶ S` (a
`k`-rational point), and let `g : Y ⟶ S` be arbitrary. Two incompatible spellings of "the fibre
of `g` over `s`" are in use:

* `Y_s = Y ×_S Spec k`, the pullback along `s` itself, which is what
  `StacksFrontier/AlgebraicGeometry/DerivedVarieties/NoDeformations/ConstantFamily.lean` uses to
  state [Stacks, Tag 0G0R]; and
* `AlgebraicGeometry.Scheme.Hom.fiber`, Mathlib's `g.fiber y = Y ×_S Spec κ(y)`, the pullback
  along `S.fromSpecResidueField y` at a *topological* point `y` of `S`, which is what the
  fibre-stalk API of
  `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreStalk.lean` is stated at
  (`AlgebraicGeometry.quotientStalkEquivFiberStalk`, in particular).

For a `k`-rational point the two agree, and this file proves it. The content is that the
canonical map `κ(s) ⟶ k` through which `s` factors is an isomorphism when `s` is a section: it
is injective because it is a map of fields, and surjective because the section splits the stalk
map of `s`.

## Main results

* `AlgebraicGeometry.isIso_descResidueField_of_isSection` — for a section `s` of
  `q : S ⟶ Spec k`, the canonical map `κ(s(pt)) ⟶ k` of
  `AlgebraicGeometry.Scheme.descResidueField` is an isomorphism. This is the statement that a
  `k`-rational point has residue field `k`.
* `AlgebraicGeometry.isPullback_fibreAtRationalPoint` — the fibre square of `g` at `s`, read as
  a square over `Spec κ(s(pt))` instead of over `Spec k`: it is a pullback square, so `Y_s` is
  the fibre of `g` at the topological point `s(pt)` in Mathlib's sense.
* `AlgebraicGeometry.fibreAtRationalPointIsoFiber` — hence an isomorphism
  `Y_s ≅ g.fiber (s(pt))`, with `AlgebraicGeometry.fibreAtRationalPointIsoFiber_hom_fiberι` and
  `AlgebraicGeometry.fibreAtRationalPointIsoFiber_hom_fiberToSpecResidueField` saying it is
  compatible with both projections, and
  `AlgebraicGeometry.fibreAtRationalPointIsoFiber_hom_over` saying it is an isomorphism of
  schemes over `Spec k`.

## Implementation notes

*Which point of `S`.* The point is `s (IsLocalRing.closedPoint k)`, the image of the unique point
of `Spec k`; this is the spelling Mathlib's
`AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField` uses, and the
factorisation of `s` through `Spec κ(s(pt))` is that lemma.

*Why surjectivity needs the section.* `κ(s(pt)) ⟶ k` is a map of fields, so injective; the
section makes it split epi, because `Spec κ(s(pt)) ⟶ S ⟶ Spec k` is `Spec` of a ring map
`k ⟶ κ(s(pt))` whose composite the other way is the identity. Without the section nothing forces
it to be onto, and the two fibres genuinely differ: for `S = Spec ℝ`, `g = 𝟙`, `k = ℂ` and
`s : Spec ℂ ⟶ Spec ℝ` the pullback `Y ×_S Spec k` is `Spec ℂ`, while the scheme-theoretic fibre
of `g` at the unique point of `Spec ℝ` is `Spec ℝ`.

*Relation to `AlgebraicGeometry.exists_isIso_residueField_hom_of_isSection`.* That statement, in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/NoDeformations/ConstantFamilyDescent.lean`, is
the existential form of the same fact and is now derived from
`AlgebraicGeometry.isIso_descResidueField_of_isSection` below; the content is proved once, here,
in the named form a canonical isomorphism of schemes needs.

*No hypothesis beyond the source's.* `g` is arbitrary: no smoothness, properness or finiteness is
used or assumed, and `q` carries no finite-type hypothesis. The only hypothesis is the section
condition `s ≫ q = 𝟙`, which is how
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/NoDeformations/ConstantFamily.lean` renders
"`s` is a `k`-rational point".

No `stacks` attribute is carried: this is a dictionary entry between two spellings of the fibre,
not a result of the source.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section RationalPoint

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- **A `k`-rational point has residue field `k`.** For a section `s` of `q : S ⟶ Spec k` the
canonical map `ψ : κ(s(pt)) ⟶ k` through which `s` factors is an isomorphism: it is injective
because its source is a field, and `Spec κ(s(pt)) ⟶ S ⟶ Spec k` is `Spec` of a ring map
`τ : k ⟶ κ(s(pt))` with `τ ≫ ψ = 𝟙`, so it is onto as well. -/
theorem isIso_descResidueField_of_isSection (hs : s ≫ q = 𝟙 _) :
    IsIso (S.descResidueField (Scheme.stalkClosedPointTo s)) := by
  set ψ := S.descResidueField (Scheme.stalkClosedPointTo s) with hψ
  have hfac : Spec.map ψ ≫
      S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)) = s :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S s
  set τ := Spec.preimage
    (S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)) ≫ q) with hτ
  have hτψ : τ ≫ ψ = 𝟙 (CommRingCat.of k) :=
    Spec.map_inj.mp (by
      rw [Spec.map_comp, Spec.map_id, hτ, Spec.map_preimage, ← Category.assoc, hfac, hs])
  exact (ConcreteCategory.isIso_iff_bijective ψ).mpr
    ⟨RingHom.injective _, fun z => ⟨τ.hom z,
      congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of k => h.hom z) hτψ⟩⟩

/-- `Spec` of the residue-field identification of a `k`-rational point. -/
theorem isIso_specMap_descResidueField_of_isSection (hs : s ≫ q = 𝟙 _) :
    IsIso (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s))) :=
  have := isIso_descResidueField_of_isSection q s hs
  inferInstance

/-- **The isomorphism `Spec k ≅ Spec κ(s(pt))` at a `k`-rational point**, through which `s`
factors as `Spec k ≅ Spec κ(s(pt)) ⟶ S`. -/
def rationalPointResidueFieldSpecIso (hs : s ≫ q = 𝟙 _) :
    Spec (.of k) ≅ Spec (S.residueField (s (IsLocalRing.closedPoint k))) :=
  haveI := isIso_specMap_descResidueField_of_isSection q s hs
  asIso (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s)))

/-- The forward map of `rationalPointResidueFieldSpecIso` is `Spec` of the canonical map
`κ(s(pt)) ⟶ k`. -/
@[simp]
theorem rationalPointResidueFieldSpecIso_hom (hs : s ≫ q = 𝟙 _) :
    (rationalPointResidueFieldSpecIso q s hs).hom =
      Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s)) :=
  rfl

/-- **`Y_s` is the scheme-theoretic fibre of `g` at `s(pt)`.** The fibre square of `g` at the
`k`-rational point `s`, with its right-hand edge read through the isomorphism
`Spec k ≅ Spec κ(s(pt))`, is the square exhibiting `Y_s` as the pullback of `g` along
`S.fromSpecResidueField (s(pt))`. -/
theorem isPullback_fibreAtRationalPoint (hs : s ≫ q = 𝟙 _) :
    IsPullback (fibreAtRationalPointι g s)
      (fibreAtRationalPointπ g s ≫
        Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s)))
      g (S.fromSpecResidueField (s (IsLocalRing.closedPoint k))) := by
  have := isIso_specMap_descResidueField_of_isSection q s hs
  have hbot : IsPullback s
      (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s))) (𝟙 S)
      (S.fromSpecResidueField (s (IsLocalRing.closedPoint k))) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id,
        Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S s]⟩
  have h := (IsPullback.of_hasPullback g s).paste_vert hbot
  rwa [Category.comp_id] at h

/-- **The fibre over a `k`-rational point is Mathlib's scheme-theoretic fibre**: an isomorphism
`Y_s ≅ g.fiber (s(pt))`. This is the identification that lets the fibre-stalk API stated at
`AlgebraicGeometry.Scheme.Hom.fiber` be used on the fibre `Y_s` of [Stacks, Tag 0G0R]. -/
def fibreAtRationalPointIsoFiber (hs : s ≫ q = 𝟙 _) :
    fibreAtRationalPoint g s ≅ g.fiber (s (IsLocalRing.closedPoint k)) :=
  (isPullback_fibreAtRationalPoint q g s hs).isoPullback

/-- The isomorphism `Y_s ≅ g.fiber (s(pt))` commutes with the projections to `Y`. -/
@[reassoc (attr := simp)]
theorem fibreAtRationalPointIsoFiber_hom_fiberι (hs : s ≫ q = 𝟙 _) :
    (fibreAtRationalPointIsoFiber q g s hs).hom ≫
        g.fiberι (s (IsLocalRing.closedPoint k)) =
      fibreAtRationalPointι g s :=
  (isPullback_fibreAtRationalPoint q g s hs).isoPullback_hom_fst

/-- The isomorphism `Y_s ≅ g.fiber (s(pt))`, followed by the projection to `Spec κ(s(pt))`, is the
projection `Y_s ⟶ Spec k` followed by `Spec k ≅ Spec κ(s(pt))`. -/
@[reassoc (attr := simp)]
theorem fibreAtRationalPointIsoFiber_hom_fiberToSpecResidueField (hs : s ≫ q = 𝟙 _) :
    (fibreAtRationalPointIsoFiber q g s hs).hom ≫
        g.fiberToSpecResidueField (s (IsLocalRing.closedPoint k)) =
      fibreAtRationalPointπ g s ≫
        Spec.map (S.descResidueField (Scheme.stalkClosedPointTo s)) :=
  (isPullback_fibreAtRationalPoint q g s hs).isoPullback_hom_snd

/-- The identification `Y_s ≅ g.fiber (s(pt))` is an isomorphism of schemes over `Spec k`: the
structure morphism of `g.fiber (s(pt))` to `Spec κ(s(pt))`, read back through
`Spec k ≅ Spec κ(s(pt))`, is the structure morphism `π : Y_s ⟶ Spec k`. -/
theorem fibreAtRationalPointIsoFiber_hom_over (hs : s ≫ q = 𝟙 _) :
    (fibreAtRationalPointIsoFiber q g s hs).hom ≫
        g.fiberToSpecResidueField (s (IsLocalRing.closedPoint k)) ≫
          (rationalPointResidueFieldSpecIso q s hs).inv =
      fibreAtRationalPointπ g s := by
  rw [← Category.assoc, fibreAtRationalPointIsoFiber_hom_fiberToSpecResidueField,
    Category.assoc, ← rationalPointResidueFieldSpecIso_hom q s hs, Iso.hom_inv_id,
    Category.comp_id]

end RationalPoint

end AlgebraicGeometry

end
