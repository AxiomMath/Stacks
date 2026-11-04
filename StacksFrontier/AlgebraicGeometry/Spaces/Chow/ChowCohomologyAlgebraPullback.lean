module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra

/-!
# Pullback of Chow cohomology classes

In the situation of Stacks 0EDT let `f : X ⟶ Y` be a morphism of good algebraic spaces over the
base. **Stacks 0ERL** remarks that there is a canonical `ℤ`-algebra map

  `f^* : A^*(Y) ⟶ A^*(X)`.

Given `c ∈ A^p(Y)` and a test space `X' ⟶ X`, the class `f^*c` caps on `CH_k(X')` as `c` does,
by thinking of `X'` as an algebraic space over `Y` through `X' ⟶ X ⟶ Y`. The three axioms of a
bivariant class for `f^*c` are those of `c` at the test spaces over `Y` obtained in this way, and
the cap operations of `f^*(c ∘ d)` and of `f^*1` are those of `f^*c ∘ f^*d` and of `1`, so `f^*`
is multiplicative on the graded pieces and the induced map of direct sums is a ring map.

## Main definitions

* `AlgebraicGeometry.Space.ChowCohomologyClass.comap`: the pullback `f^* : A^p(Y) ⟶ A^p(X)` of
  bivariant classes of degree `p`, an additive map.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.comap`: **Stacks 0ERL**, the `ℤ`-algebra map
  `f^* : A^*(Y) ⟶ A^*(X)`.

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyClass.comap_cap`: on a test space `g : X' ⟶ X`, with
  the structure morphism of `X` taken to be `f ≫ s_Y`, the class `f^*c` caps as `c` does on
  `g ≫ f : X' ⟶ Y`.
* `AlgebraicGeometry.Space.ChowCohomologyClass.comap_comp` and
  `AlgebraicGeometry.Space.ChowCohomologyClass.comap_one`: `f^*(c ∘ d) = f^*c ∘ f^*d` and
  `f^*1 = 1`.
* `AlgebraicGeometry.Space.ChowCohomologyAlgebra.comap_of`: `f^*` sends the homogeneous element
  `c ∈ A^p(Y)` to `f^*c ∈ A^p(X)`.

## Implementation notes

The structure morphism `s_X` of `X` to the base is given together with the equation
`f ≫ s_Y = s_X` saying that `f` is a morphism over the base. A test space `g : X' ⟶ X` is good
through `g ≫ s_X`, and the same space over `Y` is good through `(g ≫ f) ≫ s_Y`; these are the
same morphism, and when `s_X` is literally `f ≫ s_Y` they are the same Chow group, composition in
the ambient category of presheaves being associative on the nose. So the pullback is first built
for `s_X = f ≫ s_Y` and then carried along the equation `f ≫ s_Y = s_X`, which changes nothing
but the name of the structure morphism.

The Chow cohomology algebra is `AlgebraicGeometry.Space.ChowCohomologyAlgebra`, the direct sum of
the groups `AlgebraicGeometry.Space.ChowCohomologyClass` of bivariant classes for the identity, in
which the fibre product `X' ×_X X` of a test space is the test space itself; the product is
composition of bivariant classes.

## References

* [Stacks Project, Tag 0ERL](https://stacks.math.columbia.edu/tag/0ERL)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {D : BaseSpaceDimensionSituation.{u}}

namespace ChowCohomologyClass

/-! ### Changing the name of the structure morphism -/

section Congr

variable {X : D.Ambient}

/-- Two spellings of the structure morphism of a good algebraic space over the base give the same
group of Chow cohomology classes of degree `p`. -/
def congrStructure {s t : X ⟶ D.space} (hs : D.IsGood s) (ht : D.IsGood t) (h : s = t)
    (p : ℤ) : ChowCohomologyClass D s hs p ≃+ ChowCohomologyClass D t ht p := by
  subst h
  exact AddEquiv.refl _

/-- Changing the structure morphism to itself is the identity. -/
@[simp]
theorem congrStructure_refl {s : X ⟶ D.space} (hs : D.IsGood s) (p : ℤ)
    (c : ChowCohomologyClass D s hs p) : congrStructure hs hs rfl p c = c :=
  rfl

/-- Changing the name of the structure morphism commutes with composition of classes. -/
theorem congrStructure_comp {s t : X ⟶ D.space} (hs : D.IsGood s) (ht : D.IsGood t)
    (h : s = t) {p q : ℤ} (c : ChowCohomologyClass D s hs p)
    (d : ChowCohomologyClass D s hs q) :
    congrStructure hs ht h (p + q) (c.comp d) =
      (congrStructure hs ht h p c).comp (congrStructure hs ht h q d) := by
  subst h
  rfl

/-- Changing the name of the structure morphism sends the unit to the unit. -/
theorem congrStructure_one {s t : X ⟶ D.space} (hs : D.IsGood s) (ht : D.IsGood t)
    (h : s = t) : congrStructure hs ht h 0 one = one := by
  subst h
  rfl

end Congr

/-! ### The pullback of a class along a morphism -/

section Comap

variable {X Y : D.Ambient} {sY : Y ⟶ D.space} {hY : D.IsGood sY} {p : ℤ}

/-- The pullback `f^*c` of `c ∈ A^p(Y)` along `f : X ⟶ Y`, for `X` over the base through
`f ≫ s_Y`: on a test space `g : X' ⟶ X` it caps as `c` does on `g ≫ f : X' ⟶ Y`. -/
def comapOfComp (f : X ⟶ Y) (hX : D.IsGood (f ≫ sY)) (c : ChowCohomologyClass D sY hY p) :
    ChowCohomologyClass D (f ≫ sY) hX p where
  cap g hY' k l hkl := c.cap (g ≫ f) hY' k l hkl
  proper_naturality g hY' h hY'' hh k l hkl α :=
    c.proper_naturality (g ≫ f) hY' h hY'' hh k l hkl α
  flat_naturality g hY' h hY'' r hh hr k l hkl k' l' hk hl x :=
    c.flat_naturality (g ≫ f) hY' h hY'' r hh hr k l hkl k' l' hk hl x
  gysin_naturality g hY' L σ hL k l hkl x :=
    c.gysin_naturality (g ≫ f) hY' L σ hL k l hkl x

/-- The class `comapOfComp f hX c` caps on a test space `g : X' ⟶ X` as `c` does on
`g ≫ f : X' ⟶ Y`. -/
@[simp]
theorem comapOfComp_cap (f : X ⟶ Y) (hX : D.IsGood (f ≫ sY))
    (c : ChowCohomologyClass D sY hY p) {X' : D.Ambient} (g : X' ⟶ X)
    (hX' : D.IsGood (g ≫ f ≫ sY)) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ f ≫ sY) hX' k) :
    (comapOfComp f hX c).cap g hX' k l hkl x = c.cap (g ≫ f) hX' k l hkl x :=
  rfl

variable {sX : X ⟶ D.space} {hX : D.IsGood sX}

/-- **Stacks 0ERL, in degree `p`.** The pullback `f^* : A^p(Y) ⟶ A^p(X)` along a morphism
`f : X ⟶ Y` of good algebraic spaces over the base: given `c ∈ A^p(Y)` and a test space
`X' ⟶ X`, the class `f^*c` caps on `CH_k(X')` as `c` does, `X'` being thought of as an algebraic
space over `Y` through `X' ⟶ X ⟶ Y`. -/
def comap (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ) :
    ChowCohomologyClass D sY hY p →+ ChowCohomologyClass D sX hX p where
  toFun c := congrStructure (hf.symm ▸ hX) hX hf p (comapOfComp f (hf.symm ▸ hX) c)
  map_zero' := by
    subst hf
    rfl
  map_add' c d := by
    subst hf
    rfl

/-- On a test space `g : X' ⟶ X`, the structure morphism of `X` being `f ≫ s_Y`, the pullback
`f^*c` caps as `c` does on `g ≫ f : X' ⟶ Y`. -/
@[simp]
theorem comap_cap (f : X ⟶ Y) (hX : D.IsGood (f ≫ sY)) (c : ChowCohomologyClass D sY hY p)
    {X' : D.Ambient} (g : X' ⟶ X) (hX' : D.IsGood (g ≫ f ≫ sY)) (k l : ℤ) (hkl : l + p = k)
    (x : chowGroupCanonical.{u + 1} D (g ≫ f ≫ sY) hX' k) :
    (comap (hX := hX) f rfl p c).cap g hX' k l hkl x = c.cap (g ≫ f) hX' k l hkl x :=
  rfl

/-- Pullback is compatible with composition of classes: `f^*(c ∘ d) = f^*c ∘ f^*d`. -/
theorem comap_comp (f : X ⟶ Y) (hf : f ≫ sY = sX) {p q : ℤ}
    (c : ChowCohomologyClass D sY hY p) (d : ChowCohomologyClass D sY hY q) :
    comap (hX := hX) f hf (p + q) (c.comp d) =
      (comap (hX := hX) f hf p c).comp (comap (hX := hX) f hf q d) := by
  subst hf
  rfl

/-- Pullback sends the unit to the unit: `f^*1 = 1`. -/
theorem comap_one (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    comap (hX := hX) f hf 0 (one : ChowCohomologyClass D sY hY 0) = one := by
  subst hf
  rfl

/-- Pullback along the identity is the identity. -/
@[simp]
theorem comap_id (c : ChowCohomologyClass D sY hY p) :
    comap (hX := hY) (𝟙 Y) (Category.id_comp sY) p c = c := by
  ext g hY' k l hkl x
  rfl

/-- Pullback is functorial: `(g ≫ f)^* = g^* ∘ f^*`. -/
theorem comap_comap {Z : D.Ambient} {sZ : Z ⟶ D.space} {hZ : D.IsGood sZ} (e : Z ⟶ X)
    (he : e ≫ sX = sZ) (f : X ⟶ Y) (hf : f ≫ sY = sX) (c : ChowCohomologyClass D sY hY p) :
    comap (hX := hZ) e he p (comap (hX := hX) f hf p c) =
      comap (hX := hZ) (e ≫ f) (by rw [Category.assoc, hf, he]) p c := by
  subst hf he
  rfl

end Comap

end ChowCohomologyClass

namespace ChowCohomologyAlgebra

variable {X Y : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space}
  {hY : D.IsGood sY}

/-- **Stacks 0ERL.** The canonical `ℤ`-algebra map `f^* : A^*(Y) ⟶ A^*(X)` attached to a
morphism `f : X ⟶ Y` of good algebraic spaces over the base. On the degree `p` component it is
the pullback `AlgebraicGeometry.Space.ChowCohomologyClass.comap`: given `c ∈ A^p(Y)` and a test
space `X' ⟶ X`, the class `f^*c` caps on `CH_k(X') ⟶ CH_{k-p}(X')` as `c` does, `X'` being
thought of as an algebraic space over `Y` through `X' ⟶ X ⟶ Y`. -/
@[stacks 0ERL]
def comap (f : X ⟶ Y) (hf : f ≫ sY = sX) :
    ChowCohomologyAlgebra D sY hY →ₐ[ℤ] ChowCohomologyAlgebra D sX hX :=
  RingHom.toIntAlgHom <|
    DirectSum.toSemiring
      (fun p ↦ (DirectSum.of (ChowCohomologyClass D sX hX) p).comp
        (ChowCohomologyClass.comap (hX := hX) f hf p))
      (by
        change DirectSum.of _ 0 (ChowCohomologyClass.comap (hX := hX) f hf 0
            ChowCohomologyClass.one) = 1
        rw [ChowCohomologyClass.comap_one]
        rfl)
      (fun {p q} c d ↦ by
        change DirectSum.of _ (p + q) (ChowCohomologyClass.comap (hX := hX) f hf (p + q)
            (c.comp d)) = DirectSum.of _ p (ChowCohomologyClass.comap (hX := hX) f hf p c) *
          DirectSum.of _ q (ChowCohomologyClass.comap (hX := hX) f hf q d)
        rw [ChowCohomologyClass.comap_comp, of_mul_of])

/-- **Stacks 0ERL.** The map `f^* : A^*(Y) ⟶ A^*(X)` sends a homogeneous class `c ∈ A^p(Y)` to
the homogeneous class `f^*c ∈ A^p(X)`. -/
@[simp]
theorem comap_of (f : X ⟶ Y) (hf : f ≫ sY = sX) (p : ℤ)
    (c : ChowCohomologyClass D sY hY p) :
    comap (hX := hX) f hf (DirectSum.of _ p c) =
      DirectSum.of _ p (ChowCohomologyClass.comap (hX := hX) f hf p c) := by
  simp [comap]

end ChowCohomologyAlgebra

end AlgebraicGeometry.Space

end
