module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sets.OpenCover

/-!
# A cartesian square of schemes on a product of affine opens

Let

```
X' --f--> X
|         |
p'        p
v         v
S' --g--> S
```

be a cartesian square of schemes, let `V` be an affine open of `S`, let `U ≤ p ⁻¹ᵁ V` be an
affine open of `X` and let `V' ≤ g ⁻¹ᵁ V` be an affine open of `S'`. **Then the open
`U' = f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V'` of `X'` is affine and its ring of sections is the tensor product**

`Γ(X', U') = Γ(X, U) ⊗_{Γ(S, V)} Γ(S', V')`.

**Such opens `U'` cover `X'`**: any point of `X'` lies over a point of `X` and a point of `S'`,
and the affine opens form a basis of each of the three schemes. So this is the local description
of a base change, and it is what reduces a statement about a cartesian square of schemes to a
statement about a pushout square of rings — for instance the base change of the sheaf of
relative differentials, Stacks Tag 01V0, whose affine content is
`KaehlerDifferential.tensorKaehlerEquiv`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.inf_preimage_of_isPullback`: the open `U'` is affine.
* `AlgebraicGeometry.isPushout_appLE_of_isPullback`: the square of section rings is a pushout
  square of commutative rings.
* `AlgebraicGeometry.algebra_isPushout_appLE_of_isPullback`: the same, as
  `Algebra.IsPushout`, for algebra structures given by the maps on sections.
* `AlgebraicGeometry.isOpenCover_inf_preimage`: the opens `U'` cover `X'`.

## Implementation notes

The square of open subschemes is cartesian by `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`,
and a cartesian square of affine schemes is a pushout square on global sections by
`AlgebraicGeometry.isPushout_appTop_of_isPullback`. Everything else is bookkeeping: the global
sections of an open subscheme are identified with the sections over the open by
`AlgebraicGeometry.Scheme.Opens.topIso`, under which the map on global sections of a `resLE` is
the map on sections (`AlgebraicGeometry.Scheme.Hom.resLE_app_top`), and
`CategoryTheory.IsPushout.of_iso` transports the square along those four identifications.

The algebra form is stated with the four algebra structures as hypotheses pinned to the maps on
sections, rather than built by `RingHom.toAlgebra` inside the statement: a caller arrives with
whichever structures its own instances produced, and the two composites `Γ(S, V) ⟶ Γ(X', U')`
agree only up to the commutation of the square, so fixing one of them in the statement would
force every caller to transport.

The covering statement asks only that the square commute, not that it be cartesian: a point of
`X'` has an image in `S` computed either way round, and that is all the proof uses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X' X S' S : Scheme.{u}} {f : X' ⟶ X} {p : X ⟶ S} {p' : X' ⟶ S'} {g : S' ⟶ S}
  {V : S.Opens} {U : X.Opens} {V' : S'.Opens} {U' : X'.Opens}

/-- **In a cartesian square of schemes, the intersection of the preimages of two affine opens
over a common affine open of the base is affine.** It is the fibre product of the two over that
common open, and a fibre product of affine schemes is affine. -/
theorem IsAffineOpen.inf_preimage_of_isPullback (H : IsPullback f p' p g)
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ p ⁻¹ᵁ V)
    (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)
    (hU' : U' = f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V') :
    IsAffineOpen U' := by
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : IsAffine V'.toScheme := hV'
  exact IsAffine.of_isPullback (Scheme.Hom.isPullback_resLE H hV'V hUV hU')

/-- **In a cartesian square of schemes, the rings of sections over a product of affine opens
form a pushout square.** For `V` affine in `S`, `U ≤ p ⁻¹ᵁ V` affine in `X`, `V' ≤ g ⁻¹ᵁ V`
affine in `S'` and `U' = f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V'`, the square

```
Γ(S, V)  ⟶ Γ(X, U)
   |          |
   v          v
Γ(S', V') ⟶ Γ(X', U')
```

of maps on sections is a pushout square of commutative rings. -/
theorem isPushout_appLE_of_isPullback (H : IsPullback f p' p g)
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ p ⁻¹ᵁ V)
    (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)
    (hU' : U' = f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V') :
    IsPushout (p.appLE V U hUV) (g.appLE V V' hV'V)
      (f.appLE U U' (hU'.le.trans inf_le_left)) (p'.appLE V' U' (hU'.le.trans inf_le_right)) := by
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : IsAffine V'.toScheme := hV'
  refine (isPushout_appTop_of_isPullback
    (Scheme.Hom.isPullback_resLE H hV'V hUV hU')).of_iso V.topIso U.topIso V'.topIso U'.topIso
      ?_ ?_ ?_ ?_ <;>
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- A ring map equal to the structure map of an algebra is the `ofHom` of its `algebraMap`. -/
private theorem ofHom_algebraMap_eq {A B : CommRingCat.{u}} [Algebra A B] (φ : A ⟶ B)
    (h : ∀ r, algebraMap A B r = φ.hom r) : CommRingCat.ofHom (algebraMap A B) = φ :=
  CommRingCat.hom_ext (RingHom.ext h)

/-- **In a cartesian square of schemes, the sections over a product of affine opens are the
tensor product of the sections over the two factors.** This is
`AlgebraicGeometry.isPushout_appLE_of_isPullback` read as `Algebra.IsPushout`, for algebra
structures pinned to the maps on sections. -/
theorem algebra_isPushout_appLE_of_isPullback (H : IsPullback f p' p g)
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ p ⁻¹ᵁ V)
    (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V)
    (hU' : U' = f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V')
    [Algebra Γ(S, V) Γ(X, U)] [Algebra Γ(S, V) Γ(S', V')] [Algebra Γ(X, U) Γ(X', U')]
    [Algebra Γ(S', V') Γ(X', U')] [Algebra Γ(S, V) Γ(X', U')]
    [IsScalarTower Γ(S, V) Γ(X, U) Γ(X', U')] [IsScalarTower Γ(S, V) Γ(S', V') Γ(X', U')]
    (hp : ∀ r, algebraMap Γ(S, V) Γ(X, U) r = (p.appLE V U hUV).hom r)
    (hg : ∀ r, algebraMap Γ(S, V) Γ(S', V') r = (g.appLE V V' hV'V).hom r)
    (hf : ∀ a, algebraMap Γ(X, U) Γ(X', U') a =
      (f.appLE U U' (hU'.le.trans inf_le_left)).hom a)
    (hp' : ∀ b, algebraMap Γ(S', V') Γ(X', U') b =
      (p'.appLE V' U' (hU'.le.trans inf_le_right)).hom b) :
    Algebra.IsPushout Γ(S, V) Γ(S', V') Γ(X, U) Γ(X', U') := by
  refine (CommRingCat.isPushout_iff_isPushout (R := Γ(S, V)) (S := Γ(X, U)) (R' := Γ(S', V'))
    (S' := Γ(X', U'))).mp ?_
  rw [ofHom_algebraMap_eq _ hg, ofHom_algebraMap_eq _ hp, ofHom_algebraMap_eq _ hp',
    ofHom_algebraMap_eq _ hf]
  exact (isPushout_appLE_of_isPullback H hV hU hUV hV' hV'V hU').flip

/-- **The products of affine opens cover the corner of a commutative square.** For a commutative
square of schemes, the opens `f ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ V'` of `X'`, indexed by the triples consisting of
an affine open `V` of `S`, an affine open `U ≤ p ⁻¹ᵁ V` of `X` and an affine open
`V' ≤ g ⁻¹ᵁ V` of `S'`, form an open cover of `X'`.

A point `x` of `X'` has one image in `S`, because the square commutes; choose an affine open `V`
of `S` around it, then an affine open of `X` around `f x` inside `p ⁻¹ᵁ V` and an affine open of
`S'` around `p' x` inside `g ⁻¹ᵁ V`, all three by `AlgebraicGeometry.Scheme.isBasis_affineOpens`.
When the square is cartesian each member is affine with the expected ring of sections, by
`AlgebraicGeometry.IsAffineOpen.inf_preimage_of_isPullback` and
`AlgebraicGeometry.isPushout_appLE_of_isPullback`. -/
theorem isOpenCover_inf_preimage (hcomm : f ≫ p = p' ≫ g) :
    IsOpenCover (fun t : {t : S.Opens × X.Opens × S'.Opens // IsAffineOpen t.1 ∧
        IsAffineOpen t.2.1 ∧ t.2.1 ≤ p ⁻¹ᵁ t.1 ∧ IsAffineOpen t.2.2 ∧ t.2.2 ≤ g ⁻¹ᵁ t.1} =>
      f ⁻¹ᵁ t.1.2.1 ⊓ p' ⁻¹ᵁ t.1.2.2) := by
  refine IsOpenCover.mk (top_le_iff.1 fun x _ => ?_)
  rw [Opens.mem_iSup]
  obtain ⟨V, hV, hmemV, -⟩ := Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens
    (show p.base (f.base x) ∈ (⊤ : S.Opens) from trivial)
  have hgx : p'.base x ∈ g ⁻¹ᵁ V := by
    have hbase : g.base (p'.base x) = p.base (f.base x) :=
      (congrArg (fun q : X' ⟶ S => q.base x) hcomm).symm
    simpa [hbase] using hmemV
  obtain ⟨U, hU, hmemU, hUle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show f.base x ∈ p ⁻¹ᵁ V from hmemV)
  obtain ⟨V', hV', hmemV', hV'le⟩ := Opens.isBasis_iff_nbhd.1 S'.isBasis_affineOpens hgx
  exact ⟨⟨⟨V, U, V'⟩, hV, hU, hUle, hV', hV'le⟩, hmemU, hmemV'⟩

end AlgebraicGeometry

end
