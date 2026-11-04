module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# The threefold site of a sequence of ring maps, and the three morphisms of ringed topoi

Let `A → B → C` be ring maps. A *polynomial tower* for them is a pair `(P → B, Q → C)` in which
`P` is a polynomial `A`-algebra, `P → B` a map of `A`-algebras, `Q` a polynomial `P`-algebra and
`Q → C` a map of `P`-algebras; a morphism of towers is a pair of maps `P → P'` over `B` and
`Q → Q'` over `C` commuting with `P → Q` and `P' → Q'`. The site `C_{C/B/A}` is the *opposite* of
the category of polynomial towers, so that an object of it is the commutative diagram of spectra

```
Spec C --→ Spec Q
  |          |
Spec B --→ Spec P --→ Spec A
```

It carries the chaotic topology, so every presheaf on it is a sheaf.

Three functors land in the three two-term sites of
`StacksFrontier.Cotangent.PolynomialAlgebraSite`:

```
u₁ (P → B, Q → C) = (P → B)         ∈ C_{B/A}
u₂ (P → B, Q → C) = (Q → C)         ∈ C_{C/A}
u₃ (P → B, Q → C) = (Q ⊗_P B → C)   ∈ C_{C/B}
```

Each is both continuous and cocontinuous, because all four sites are chaotic, and therefore
induces a morphism of topoi `gᵢ`. Writing `𝒪ᵢ = gᵢ⁻¹𝒪` for the inverse image of the tautological
sheaf of rings of the target makes each `gᵢ` a morphism of *ringed* topoi

```
g₁ : (Sh(C_{C/B/A}), 𝒪₁) ⟶ (Sh(C_{B/A}), 𝒪)
g₂ : (Sh(C_{C/B/A}), 𝒪₂) ⟶ (Sh(C_{C/A}), 𝒪)
g₃ : (Sh(C_{C/B/A}), 𝒪₃) ⟶ (Sh(C_{C/B}), 𝒪)
```

which is the display (92.7.0.2) of Tag 08QT. Finally, writing `π, π₁, π₂, π₃` for the
projections of the four sites to the point, one has `π = πᵢ ∘ gᵢ` for `i = 1, 2, 3`.

## Main definitions

* `CommAlgCat.TowerComma`: triples `(P → B, Q → C, P → Q)` with no condition imposed, the
  comma category in which the towers live.
* `CommAlgCat.IsPolynomialTower` and `CommAlgCat.PolynomialTower`: the two conditions on such a
  triple, and the category of polynomial towers they cut out.
* `CommAlgCat.polynomialTowerSite`: the site `C_{C/B/A}`.
* `CommAlgCat.polynomialTowerRingedPoint` and `CommAlgCat.polynomialTowerTopology`: the ringed
  point of Tag 08PF attached to `C_{C/B/A}` and the ring `C`, and the topology it produces.
* `CommAlgCat.polynomialTowerFirst`, `CommAlgCat.polynomialTowerSecond`,
  `CommAlgCat.polynomialTowerThird`: the three functors `u₁`, `u₂`, `u₃` of sites, each the
  opposite of a functor `CommAlgCat.polynomialTower*Augmentations` of the underlying categories
  of augmented algebras.
* `CommAlgCat.towerBaseChangeAlgebra`, `CommAlgCat.towerBaseChangeAugmentation` and
  `CommAlgCat.towerBaseChangeMap`: the algebra `Q ⊗_P B`, its augmentation to `C` and the action
  of `u₃` on a morphism of towers.
* `CommAlgCat.polynomialTowerFirstTopos`, `...SecondTopos`, `...ThirdTopos`: the three morphisms
  of topoi `g₁`, `g₂`, `g₃`.
* `CommAlgCat.polynomialTowerFirstStructureSheaf`, `...SecondStructureSheaf`,
  `...ThirdStructureSheaf`: the three sheaves of rings `𝒪ᵢ = gᵢ⁻¹𝒪`.
* `CommAlgCat.polynomialTowerFirstRinged`, `...SecondRinged`, `...ThirdRinged`: the three
  morphisms of ringed topoi, i.e. the display of Tag 08QT.
* `CommAlgCat.polynomialTowerProjection` and `CommAlgCat.polynomialTowerFirstProjection`,
  `...SecondProjection`, `...ThirdProjection`: the projections `π`, `π₁`, `π₂`, `π₃` to the
  point.

## Main results

* `CommAlgCat.polynomialTowerTopology_eq_bot`: the topology of `C_{C/B/A}` is the chaotic one.
* `CommAlgCat.isPolynomialAlgebra_towerRightAlgebra`: the algebra `Q` of a polynomial tower is a
  polynomial algebra over `A`, since `A[ι][κ] = A[κ ⊕ ι]`. This is what makes `u₂` land in
  `C_{C/A}`.
* `CommAlgCat.isPolynomialAlgebra_towerBaseChangeAlgebra`: `Q ⊗_P B` is a polynomial algebra
  over `B`, since `P[κ] ⊗_P B = B[κ]`. This is what makes `u₃` land in `C_{C/B}`.
* `CommAlgCat.towerBaseChangeAugmentation_tmul` and `CommAlgCat.towerBaseChangeMap_tmul`: the
  augmentation and the action on morphisms of `u₃`, on a pure tensor.
* `CommAlgCat.polynomialTowerFirstTopos_inverseImage` and its two siblings: the inverse image of
  `gᵢ` is restriction along `uᵢ`.
* `CommAlgCat.polynomialTowerFirstProjection_comp_inverseImage` and its two siblings, together
  with `CommAlgCat.polynomialTowerFirstProjection_comp_pushforwardIso` and its two siblings:
  the identity `π = πᵢ ∘ gᵢ`. The inverse images are equal on the nose and the direct images are
  canonically isomorphic; see the implementation notes.
* `Stacks.ChaoticSite.isContinuous_of_eq_bot` and
  `Stacks.ChaoticSite.isCocontinuous_of_eq_bot`: a functor is continuous as soon as its source
  carries the chaotic topology, and cocontinuous as soon as its target does.

## Implementation notes

The category of towers is the full subcategory of the comma category
`Comma (towerLeftForget A B) (Over.forget (towerTotalAlgebra A C))` cut out by the two
conditions on an object, so its category structure — and with it the action of `u₁` and `u₂` on
morphisms — is the existing one rather than a new one. The first factor of the comma category is
the category `CommAlgCat.PolynomialAugmentation` of Tag 08PR, so `u₁` is a projection, and the
three target sites are the ones built there rather than parallel copies.

`P` is not a base ring of the ambient setting, so the `P`-algebra structures of `Q`, `B` and `C`
cannot be section variables; they are recorded as instances attached to an object of the comma
category (`CommAlgCat.towerAlgebraRight` and its siblings), each read off the corresponding map
of `A`-algebras. With those in place every scalar tower that `Q ⊗_P B` needs is found by
instance search: in particular `Algebra ↑P (B ⊗[↑P'] ↑Q')` and
`IsScalarTower ↑P B (B ⊗[↑P'] ↑Q')`, which are what make `u₃` functorial, are Mathlib's
`Algebra.TensorProduct.leftAlgebra` for the left factor.

`u₃` is a genuine definition and not a choice: `towerBaseChangeAlgebra` is the tensor product
`B ⊗_P Q` itself, `towerBaseChangeAugmentation` and `towerBaseChangeMap` are built from the
universal property through `Algebra.TensorProduct.productLeftAlgHom`, and
`towerBaseChangeAugmentation_tmul` and `towerBaseChangeMap_tmul` pin both down on a pure tensor.

Each `gᵢ` is `CategoryTheory.Functor.morphismOfTopoiOfCocontinuous` for `uᵢ`, so `gᵢ⁻¹` *is*
restriction along `uᵢ` and `gᵢ_*` *is* the right Kan extension along `uᵢ.op`. Its universes are
given explicitly: left to unification, the universe of the sheaves of sets is solved against
`max (u+1) ?w` and the elaboration gets stuck. The structure map of the ringed `gᵢ` is the unit
of the ring-level adjunction `gᵢ⁻¹ ⊣ gᵢ_*` at `𝒪`, which is the only choice compatible with
`𝒪ᵢ = gᵢ⁻¹𝒪` — and `polynomialTowerFirstRingedTopos_O` and its siblings record that the source's
structure sheaf is that inverse image.

`π = πᵢ ∘ gᵢ` is stated as the pair (equality of inverse images, canonical isomorphism of direct
images), which is how this development states a commutative triangle of topoi everywhere else
(compare the fields `inverseImageComparison` and `commutativityIso` of
`Stacks.Sites.FibredCategory.MorphismSituation.RingedToposDiagram`). The equality of inverse
images holds on the nose, by `rfl`: `uᵢ` followed by the unique functor to the point *is* the
unique functor to the point, and restriction along a composite is the composite of the
restrictions. A strict equality of the whole `MorphismOfTopoi` is not available and is not what
the source asserts: the direct image is a right Kan extension, computed from the chosen limit
cones of `Type (u+1)`, and `ran (uᵢ.op ⋙ star.op)` and `ran uᵢ.op ⋙ ran star.op` are built from
different chosen cones. (`rfl` on the full equality reports
`Not a definitional equality` and names `getLimitCone` as the constant it declined to unfold.)
The isomorphism is therefore the canonical one between two right adjoints of one functor,
`CategoryTheory.Adjunction.rightAdjointUniq`, exactly as Tag 08PA's triangle does it.

`A`, `B` and `C` share one universe, as they must: a single topos over `C_{C/B/A}` maps to all
three two-term sites, so all three need the same universe of sections, and by Tag 08PR that
universe is the one of the augmentation target.

## References

* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Section 08QR](https://stacks.math.columbia.edu/tag/08QR)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u u₁ u₂ v₁ v₂

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-! ### The three two-term sites -/

/-- `B` as an object of `CommAlgCat A`. -/
abbrev towerBaseAlgebra : CommAlgCat.{u} A := CommAlgCat.of A B

/-- `C` as an object of `CommAlgCat A`. -/
abbrev towerTotalAlgebra : CommAlgCat.{u} A := CommAlgCat.of A C

/-- `C` as an object of `CommAlgCat B`. -/
abbrev towerRelativeAlgebra : CommAlgCat.{u} B := CommAlgCat.of B C

/-- The map `B → C`, as a morphism of `A`-algebras. -/
abbrev towerBaseToTotal : towerBaseAlgebra A B ⟶ towerTotalAlgebra A C :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C)

/-! ### The category of polynomial towers -/

/-- `(P → B) ↦ P`, the underlying `A`-algebra of a polynomial `A`-algebra augmented to `B`. -/
abbrev towerLeftForget :
    PolynomialAugmentation A (towerBaseAlgebra A B) ⥤ CommAlgCat.{u} A :=
  (IsPolynomialAlgebraOver A (towerBaseAlgebra A B)).ι ⋙ Over.forget (towerBaseAlgebra A B)

/-- Triples `(P → B, Q → C, P → Q)` consisting of a polynomial `A`-algebra `P` augmented to `B`,
an `A`-algebra `Q` augmented to `C`, and a map of `A`-algebras `P → Q`. No further condition is
imposed; the conditions of a polynomial tower are `CommAlgCat.IsPolynomialTower`. -/
abbrev TowerComma :=
  Comma (towerLeftForget A B) (Over.forget (towerTotalAlgebra A C))

variable {A B C}

/-- The polynomial `A`-algebra `P` of a tower. -/
abbrev towerLeftAlgebra (X : TowerComma A B C) : CommAlgCat.{u} A := X.left.obj.left

/-- The `A`-algebra `Q` of a tower. -/
abbrev towerRightAlgebra (X : TowerComma A B C) : CommAlgCat.{u} A := X.right.left

/-- `P` acts on `Q` through the map `P → Q` of the tower. -/
instance towerAlgebraRight (X : TowerComma A B C) :
    Algebra ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X) :=
  (CommAlgCat.Hom.hom X.hom).toRingHom.toAlgebra

/-- The map `P → Q` of a tower is a map of `A`-algebras, so `A` acts on `Q` through `P`. -/
instance towerIsScalarTowerRight (X : TowerComma A B C) :
    IsScalarTower A ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X) :=
  IsScalarTower.of_algebraMap_eq fun a => ((CommAlgCat.Hom.hom X.hom).commutes a).symm

/-- The augmentation `P → B` of a tower makes `B` an algebra over `P`. -/
instance towerAlgebraBase (X : TowerComma A B C) : Algebra ↑(towerLeftAlgebra X) B :=
  (CommAlgCat.Hom.hom X.left.obj.hom).toRingHom.toAlgebra

/-- The augmentation `P → B` of a tower is a map of `A`-algebras, so `A` acts on `B`
through `P`. -/
instance towerIsScalarTowerBase (X : TowerComma A B C) :
    IsScalarTower A ↑(towerLeftAlgebra X) B :=
  IsScalarTower.of_algebraMap_eq fun a =>
    ((CommAlgCat.Hom.hom X.left.obj.hom).commutes a).symm

/-- `P` acts on `C` through `P → B → C`. -/
instance towerAlgebraTotal (X : TowerComma A B C) : Algebra ↑(towerLeftAlgebra X) C :=
  ((algebraMap B C).comp (algebraMap ↑(towerLeftAlgebra X) B)).toAlgebra

/-- By construction the action of `P` on `C` factors through `B`. -/
instance towerIsScalarTowerTotal (X : TowerComma A B C) :
    IsScalarTower ↑(towerLeftAlgebra X) B C :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (A B C)

/-- The two conditions on a tower `(P → B, Q → C, P → Q)` that make it a *polynomial tower*:
`Q` is a polynomial algebra over `P`, and the composite `P → Q → C` agrees with
`P → B → C`. -/
abbrev IsPolynomialTower : ObjectProperty (TowerComma A B C) := fun X =>
  IsPolynomialAlgebra ↑(towerLeftAlgebra X)
      (CommAlgCat.of ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X)) ∧
    X.hom ≫ X.right.hom = X.left.obj.hom ≫ towerBaseToTotal A B C

/-- The category of polynomial towers `(P → B, Q → C)`: `P` is a polynomial `A`-algebra with an
`A`-algebra map to `B`, `Q` is a polynomial `P`-algebra, and `Q → C` is a `P`-algebra map. -/
abbrev PolynomialTower := (IsPolynomialTower A B C).FullSubcategory

/-- The site `C_{C/B/A}`: the opposite of the category of polynomial towers `(P → B, Q → C)`,
so that an object corresponds to the commutative diagram of spectra in which
`Spec C → Spec Q` lies over `Spec B → Spec P` over `Spec A`. -/
@[stacks 08QT "the site C_{C/B/A}"]
abbrev polynomialTowerSite := (PolynomialTower A B C)ᵒᵖ

/-- The ringed point attached to the site `C_{C/B/A}` and the ring `C`, from which its chaotic
topology and its projection `π` to the point are produced. -/
def polynomialTowerRingedPoint : Stacks.ChaoticSite.RingedPointSituation.{u, u, u + 1} where
  C := polynomialTowerSite A B C
  B := CommRingCat.of (ULift.{u + 1} C)

/-- The topology of the site `C_{C/B/A}`. -/
abbrev polynomialTowerTopology : GrothendieckTopology (polynomialTowerSite A B C) :=
  (polynomialTowerRingedPoint A B C).fibredSituation.topology

/-- The topology of `C_{C/B/A}` is the chaotic topology: its only coverings are the maximal
sieves, so every presheaf on `C_{C/B/A}` is a sheaf. -/
@[stacks 08QT "the chaotic topology on C_{C/B/A}"]
theorem polynomialTowerTopology_eq_bot : polynomialTowerTopology A B C = ⊥ :=
  ((polynomialTowerRingedPoint A B C).topology_eq_trivial).trans
    GrothendieckTopology.trivial_eq_bot

/-! ### The functors `u₁` and `u₂` -/

/-- `u₁ : (P → B, Q → C) ↦ (P → B)`, before passing to opposite categories. -/
def polynomialTowerFirstAugmentations :
    PolynomialTower A B C ⥤ PolynomialAugmentation A (towerBaseAlgebra A B) :=
  (IsPolynomialTower A B C).ι ⋙ Comma.fst _ _

/-- `u₁ : C_{C/B/A} ⥤ C_{B/A}`, the functor `(P → B, Q → C) ↦ (P → B)`. -/
@[stacks 08QT "the functor u₁"]
def polynomialTowerFirst : polynomialTowerSite A B C ⥤ polynomialSite A (towerBaseAlgebra A B) :=
  (polynomialTowerFirstAugmentations A B C).op

variable {A B C}

/-- The `A`-algebra `Q` of a polynomial tower is a polynomial algebra over `A`: it is a
polynomial algebra over the polynomial `A`-algebra `P`, and
`P[κ] = A[ι][κ] = A[κ ⊕ ι]`. This is what makes `u₂` land in `C_{C/A}`. -/
@[stacks 08QT "u₂ lands in C_{C/A}"]
theorem isPolynomialAlgebra_towerRightAlgebra (X : PolynomialTower A B C) :
    IsPolynomialAlgebra A (towerRightAlgebra X.obj) := by
  obtain ⟨ι, ⟨e₁⟩⟩ := X.obj.left.property
  obtain ⟨κ, ⟨e₂⟩⟩ := X.property.1
  refine ⟨κ ⊕ ι, ⟨?_⟩⟩
  have hA : ∀ a : A,
      e₂ (algebraMap A (MvPolynomial κ ↑(towerLeftAlgebra X.obj)) a) =
        algebraMap A ↑(towerRightAlgebra X.obj) a := fun a => by
    rw [IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra X.obj)
        (MvPolynomial κ ↑(towerLeftAlgebra X.obj)) a, e₂.commutes,
      ← IsScalarTower.algebraMap_apply A ↑(towerLeftAlgebra X.obj)
        ↑(towerRightAlgebra X.obj) a]
  exact (MvPolynomial.sumAlgEquiv A κ ι).trans
    ((MvPolynomial.mapAlgEquiv κ e₁).trans (AlgEquiv.ofRingEquiv (f := e₂.toRingEquiv) hA))

variable (A B C)

/-- `u₂ : (P → B, Q → C) ↦ (Q → C)`, before passing to opposite categories. -/
def polynomialTowerSecondAugmentations :
    PolynomialTower A B C ⥤ PolynomialAugmentation A (towerTotalAlgebra A C) :=
  (IsPolynomialAlgebraOver A (towerTotalAlgebra A C)).lift
    ((IsPolynomialTower A B C).ι ⋙ Comma.snd _ _)
    fun X => isPolynomialAlgebra_towerRightAlgebra X

/-- `u₂ : C_{C/B/A} ⥤ C_{C/A}`, the functor `(P → B, Q → C) ↦ (Q → C)`. -/
@[stacks 08QT "the functor u₂"]
def polynomialTowerSecond :
    polynomialTowerSite A B C ⥤ polynomialSite A (towerTotalAlgebra A C) :=
  (polynomialTowerSecondAugmentations A B C).op

/-! ### The functor `u₃` -/

variable {A B C}

/-- The tower condition, read on elements: the composite `P → Q → C` of a polynomial tower is
`P → B → C`. -/
theorem towerRight_hom_towerMap_apply (X : PolynomialTower A B C)
    (p : ↑(towerLeftAlgebra X.obj)) :
    (CommAlgCat.Hom.hom X.obj.right.hom) ((CommAlgCat.Hom.hom X.obj.hom) p) =
      algebraMap B C ((CommAlgCat.Hom.hom X.obj.left.obj.hom) p) :=
  congrArg (fun k => (CommAlgCat.Hom.hom k) p) X.property.2

/-- The augmentation `Q → C` of a polynomial tower, read as a map of `P`-algebras. This is the
content of the tower condition: `P → Q → C` is `P → B → C`, which is the structure map of `C`
as a `P`-algebra. -/
def towerRightAugmentation (X : PolynomialTower A B C) :
    ↑(towerRightAlgebra X.obj) →ₐ[↑(towerLeftAlgebra X.obj)] C where
  toRingHom := (CommAlgCat.Hom.hom X.obj.right.hom).toRingHom
  commutes' p := towerRight_hom_towerMap_apply X p

/-- `Q ⊗_P B`, as an object of `CommAlgCat B`. It is the pushout of `B ← P → Q`, realised as the
tensor product of `B` and `Q` over `P`, with `B` acting through the left factor. -/
abbrev towerBaseChangeAlgebra (X : TowerComma A B C) : CommAlgCat.{u} B :=
  CommAlgCat.of B (B ⊗[↑(towerLeftAlgebra X)] ↑(towerRightAlgebra X))

/-- The augmentation `Q ⊗_P B → C` of the base-changed algebra: `b ⊗ q ↦ b · β(q)`, where
`β : Q → C` is the augmentation of the tower. -/
def towerBaseChangeAugmentation (X : PolynomialTower A B C) :
    ↑(towerBaseChangeAlgebra X.obj) →ₐ[B] C :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId B C) (towerRightAugmentation X)

/-- The augmentation of the base-changed algebra on a pure tensor. -/
@[simp]
theorem towerBaseChangeAugmentation_tmul (X : PolynomialTower A B C) (b : B)
    (q : ↑(towerRightAlgebra X.obj)) :
    towerBaseChangeAugmentation X (b ⊗ₜ[↑(towerLeftAlgebra X.obj)] q) =
      algebraMap B C b * (CommAlgCat.Hom.hom X.obj.right.hom) q := by
  simp [towerBaseChangeAugmentation, towerRightAugmentation, Algebra.ofId_apply]

omit [Algebra B C] [IsScalarTower A B C] in
/-- The augmentation `P → B` of a tower is natural: `P → P' → B` is `P → B`. -/
theorem towerLeft_hom_apply {X Y : TowerComma A B C} (g : X ⟶ Y)
    (p : ↑(towerLeftAlgebra X)) :
    algebraMap ↑(towerLeftAlgebra Y) B ((CommAlgCat.Hom.hom g.left.hom.left) p) =
      algebraMap ↑(towerLeftAlgebra X) B p :=
  congrArg (fun k => (CommAlgCat.Hom.hom k) p) (Over.w g.left.hom)

omit [Algebra B C] [IsScalarTower A B C] in
/-- A morphism of towers commutes with the maps `P → Q`. -/
theorem towerRight_hom_apply {X Y : TowerComma A B C} (g : X ⟶ Y)
    (p : ↑(towerLeftAlgebra X)) :
    (CommAlgCat.Hom.hom g.right.left)
        (algebraMap ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X) p) =
      algebraMap ↑(towerLeftAlgebra Y) ↑(towerRightAlgebra Y)
        ((CommAlgCat.Hom.hom g.left.hom.left) p) :=
  (congrArg (fun k => (CommAlgCat.Hom.hom k) p) g.w).symm

/-- The map `q ↦ 1 ⊗ ψ(q)` from `Q` to `Q' ⊗_{P'} B`, as a map of `P`-algebras. It is the
second leg of the universal property that defines `u₃` on morphisms. -/
def towerBaseChangeRightLeg {X Y : TowerComma A B C} (g : X ⟶ Y) :
    ↑(towerRightAlgebra X) →ₐ[↑(towerLeftAlgebra X)] ↑(towerBaseChangeAlgebra Y) where
  toFun q := 1 ⊗ₜ[↑(towerLeftAlgebra Y)] (CommAlgCat.Hom.hom g.right.left) q
  map_one' := by
    simp only [map_one]
    exact Algebra.TensorProduct.one_def.symm
  map_mul' x y := by simp [Algebra.TensorProduct.tmul_mul_tmul]
  map_zero' := by simp
  map_add' x y := by simp [TensorProduct.tmul_add]
  commutes' p := by
    change (1 : B) ⊗ₜ[↑(towerLeftAlgebra Y)]
        (CommAlgCat.Hom.hom g.right.left)
          (algebraMap ↑(towerLeftAlgebra X) ↑(towerRightAlgebra X) p) =
      algebraMap ↑(towerLeftAlgebra X) ↑(towerBaseChangeAlgebra Y) p
    rw [towerRight_hom_apply g p, Algebra.TensorProduct.algebraMap_def]
    change _ = (algebraMap ↑(towerLeftAlgebra X) B p) ⊗ₜ[↑(towerLeftAlgebra Y)]
      (1 : ↑(towerRightAlgebra Y))
    rw [← towerLeft_hom_apply g p, Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- `u₃` on a morphism of towers: the map `Q ⊗_P B → Q' ⊗_{P'} B` determined by `Q → Q'` and
the identity of `B`. -/
def towerBaseChangeMap {X Y : TowerComma A B C} (g : X ⟶ Y) :
    ↑(towerBaseChangeAlgebra X) →ₐ[B] ↑(towerBaseChangeAlgebra Y) :=
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId B ↑(towerBaseChangeAlgebra Y)) (towerBaseChangeRightLeg g)

omit [Algebra B C] [IsScalarTower A B C] in
/-- `u₃` on a morphism, evaluated on a pure tensor: `b ⊗ q ↦ b ⊗ ψ(q)`. This pins the map down;
it is not a chosen solution of a universal property. -/
@[simp]
theorem towerBaseChangeMap_tmul {X Y : TowerComma A B C} (g : X ⟶ Y) (b : B)
    (q : ↑(towerRightAlgebra X)) :
    towerBaseChangeMap g (b ⊗ₜ[↑(towerLeftAlgebra X)] q) =
      b ⊗ₜ[↑(towerLeftAlgebra Y)] (CommAlgCat.Hom.hom g.right.left) q := by
  show algebraMap B ↑(towerBaseChangeAlgebra Y) b *
      (1 ⊗ₜ[↑(towerLeftAlgebra Y)] (CommAlgCat.Hom.hom g.right.left) q) = _
  rw [Algebra.TensorProduct.algebraMap_def]
  show (b ⊗ₜ[↑(towerLeftAlgebra Y)] (1 : ↑(towerRightAlgebra Y))) *
      (1 ⊗ₜ[↑(towerLeftAlgebra Y)] (CommAlgCat.Hom.hom g.right.left) q) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [Algebra B C] [IsScalarTower A B C] in
/-- The augmentation `Q → C` of a tower is natural: `Q → Q' → C` is `Q → C`. -/
theorem towerRightAugmentation_hom_apply {X Y : TowerComma A B C} (g : X ⟶ Y)
    (q : ↑(towerRightAlgebra X)) :
    (CommAlgCat.Hom.hom Y.right.hom) ((CommAlgCat.Hom.hom g.right.left) q) =
      (CommAlgCat.Hom.hom X.right.hom) q :=
  congrArg (fun k => (CommAlgCat.Hom.hom k) q) (Over.w g.right)

/-- `u₃` is compatible with the augmentations to `C`. -/
theorem towerBaseChangeMap_comp_augmentation {X Y : PolynomialTower A B C} (g : X ⟶ Y) :
    CommAlgCat.ofHom (towerBaseChangeMap g.hom) ≫
        CommAlgCat.ofHom (towerBaseChangeAugmentation Y) =
      CommAlgCat.ofHom (towerBaseChangeAugmentation X) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  show (towerBaseChangeAugmentation Y) ((towerBaseChangeMap g.hom) z) =
    (towerBaseChangeAugmentation X) z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b q =>
      rw [towerBaseChangeMap_tmul, towerBaseChangeAugmentation_tmul,
        towerBaseChangeAugmentation_tmul, towerRightAugmentation_hom_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `Q ⊗_P B` is a polynomial algebra over `B`: if `Q = P[κ]` then `Q ⊗_P B = B[κ]`. This is
what makes `u₃` land in `C_{C/B}`. -/
@[stacks 08QT "u₃ lands in C_{C/B}"]
theorem isPolynomialAlgebra_towerBaseChangeAlgebra (X : PolynomialTower A B C) :
    IsPolynomialAlgebra B (towerBaseChangeAlgebra X.obj) := by
  obtain ⟨κ, ⟨e⟩⟩ := X.property.1
  refine ⟨κ, ⟨?_⟩⟩
  have hf : Function.Bijective
      (Algebra.TensorProduct.map (S := B) (AlgHom.id B B) e.toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id B B).restrictScalars ↑(towerLeftAlgebra X.obj)) (g := e.toAlgHom)
      Function.bijective_id e.bijective
  exact (MvPolynomial.scalarRTensorAlgEquiv
      (R := ↑(towerLeftAlgebra X.obj)) (N := B) (σ := κ)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id B B) e.toAlgHom) hf)

variable (A B C)

/-- `u₃ : (P → B, Q → C) ↦ (Q ⊗_P B → C)`, as a functor to the `B`-algebras augmented to `C`. -/
def towerBaseChangeOver : PolynomialTower A B C ⥤ Over (towerRelativeAlgebra B C) where
  obj X := Over.mk (CommAlgCat.ofHom (towerBaseChangeAugmentation X))
  map {_ _} g := Over.homMk (CommAlgCat.ofHom (towerBaseChangeMap g.hom))
    (towerBaseChangeMap_comp_augmentation g)
  map_id X := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change (towerBaseChangeMap (𝟙 X.obj)) z = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b q =>
        rw [towerBaseChangeMap_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_comp {X Y Z} g h := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change (towerBaseChangeMap (g.hom ≫ h.hom)) z =
      (towerBaseChangeMap h.hom) ((towerBaseChangeMap g.hom) z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b q =>
        rw [towerBaseChangeMap_tmul, towerBaseChangeMap_tmul, towerBaseChangeMap_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- `u₃ : (P → B, Q → C) ↦ (Q ⊗_P B → C)`, before passing to opposite categories. -/
def polynomialTowerThirdAugmentations :
    PolynomialTower A B C ⥤ PolynomialAugmentation B (towerRelativeAlgebra B C) :=
  (IsPolynomialAlgebraOver B (towerRelativeAlgebra B C)).lift (towerBaseChangeOver A B C)
    fun X => isPolynomialAlgebra_towerBaseChangeAlgebra X

/-- `u₃ : C_{C/B/A} ⥤ C_{C/B}`, the functor `(P → B, Q → C) ↦ (Q ⊗_P B → C)`. -/
@[stacks 08QT "the functor u₃"]
def polynomialTowerThird :
    polynomialTowerSite A B C ⥤ polynomialSite B (towerRelativeAlgebra B C) :=
  (polynomialTowerThirdAugmentations A B C).op

/-! ### What the three functors do -/

/-- `u₁` on objects: the first component `(P → B)` of the tower. -/
theorem polynomialTowerFirstAugmentations_obj (X : PolynomialTower A B C) :
    (polynomialTowerFirstAugmentations A B C).obj X = X.obj.left := rfl

/-- `u₁` on morphisms: the first component of the morphism of towers. -/
theorem polynomialTowerFirstAugmentations_map {X Y : PolynomialTower A B C} (g : X ⟶ Y) :
    (polynomialTowerFirstAugmentations A B C).map g = g.hom.left := rfl

/-- `u₂` on objects: the second component `(Q → C)` of the tower. -/
theorem polynomialTowerSecondAugmentations_obj_obj (X : PolynomialTower A B C) :
    ((polynomialTowerSecondAugmentations A B C).obj X).obj = X.obj.right := rfl

/-- `u₂` on morphisms: the second component of the morphism of towers. -/
theorem polynomialTowerSecondAugmentations_map_hom {X Y : PolynomialTower A B C} (g : X ⟶ Y) :
    ((polynomialTowerSecondAugmentations A B C).map g).hom = g.hom.right := rfl

/-- `u₃` on objects: the algebra is `Q ⊗_P B`. -/
theorem polynomialTowerThirdAugmentations_obj_obj_left (X : PolynomialTower A B C) :
    ((polynomialTowerThirdAugmentations A B C).obj X).obj.left =
      towerBaseChangeAlgebra X.obj := rfl

/-- `u₃` on objects: the augmentation is the one of
`CommAlgCat.towerBaseChangeAugmentation`. -/
theorem polynomialTowerThirdAugmentations_obj_obj_hom (X : PolynomialTower A B C) :
    ((polynomialTowerThirdAugmentations A B C).obj X).obj.hom =
      CommAlgCat.ofHom (towerBaseChangeAugmentation X) := rfl

/-- `u₃` on morphisms: the map of `CommAlgCat.towerBaseChangeMap`. -/
theorem polynomialTowerThirdAugmentations_map_hom_left {X Y : PolynomialTower A B C}
    (g : X ⟶ Y) :
    ((polynomialTowerThirdAugmentations A B C).map g).hom.left =
      CommAlgCat.ofHom (towerBaseChangeMap g.hom) := rfl

/-! ### The three morphisms of topoi -/

/-- Any functor is continuous when its source carries the chaotic topology: for the chaotic
topology every presheaf is a sheaf, so there is nothing to check. -/
theorem _root_.Stacks.ChaoticSite.isContinuous_of_eq_bot {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : D ⥤ E) (JD : GrothendieckTopology D)
    (JE : GrothendieckTopology E) (h : JD = ⊥) : F.IsContinuous JD JE where
  op_comp_isSheaf_of_types _ := by subst h; exact Presieve.isSheaf_bot

/-- Any functor is cocontinuous when its target carries the chaotic topology: the only covering
sieve of the target is the maximal one, whose pullback is maximal. -/
theorem _root_.Stacks.ChaoticSite.isCocontinuous_of_eq_bot {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E] (F : D ⥤ E) (JD : GrothendieckTopology D)
    (JE : GrothendieckTopology E) (h : JE = ⊥) : F.IsCocontinuous JD JE where
  cover_lift {U} {S} hS := by
    subst h
    rw [GrothendieckTopology.bot_covering] at hS
    subst hS
    simp

/-- The functor `u₁` is continuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerFirst_isContinuous :
    (polynomialTowerFirst A B C).IsContinuous (polynomialTowerTopology A B C)
      (polynomialTopology A (towerBaseAlgebra A B)) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ (polynomialTowerTopology_eq_bot A B C)

/-- The functor `u₁` is cocontinuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerFirst_isCocontinuous :
    (polynomialTowerFirst A B C).IsCocontinuous (polynomialTowerTopology A B C)
      (polynomialTopology A (towerBaseAlgebra A B)) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _
    (polynomialTopology_eq_bot A (towerBaseAlgebra A B))

/-- The functor `u₂` is continuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerSecond_isContinuous :
    (polynomialTowerSecond A B C).IsContinuous (polynomialTowerTopology A B C)
      (polynomialTopology A (towerTotalAlgebra A C)) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ (polynomialTowerTopology_eq_bot A B C)

/-- The functor `u₂` is cocontinuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerSecond_isCocontinuous :
    (polynomialTowerSecond A B C).IsCocontinuous (polynomialTowerTopology A B C)
      (polynomialTopology A (towerTotalAlgebra A C)) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _
    (polynomialTopology_eq_bot A (towerTotalAlgebra A C))

/-- The functor `u₃` is continuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerThird_isContinuous :
    (polynomialTowerThird A B C).IsContinuous (polynomialTowerTopology A B C)
      (polynomialTopology B (towerRelativeAlgebra B C)) :=
  Stacks.ChaoticSite.isContinuous_of_eq_bot _ _ _ (polynomialTowerTopology_eq_bot A B C)

/-- The functor `u₃` is cocontinuous with respect to the chaotic topologies on both sites. -/
instance polynomialTowerThird_isCocontinuous :
    (polynomialTowerThird A B C).IsCocontinuous (polynomialTowerTopology A B C)
      (polynomialTopology B (towerRelativeAlgebra B C)) :=
  Stacks.ChaoticSite.isCocontinuous_of_eq_bot _ _ _
    (polynomialTopology_eq_bot B (towerRelativeAlgebra B C))

/-- `g₁ : Sh(C_{C/B/A}) ⟶ Sh(C_{B/A})`, the morphism of topoi induced by `u₁`. Its inverse
image is restriction along `u₁`. -/
def polynomialTowerFirstTopos :
    MorphismOfTopoi (Sheaf (polynomialTowerTopology A B C) (Type (u + 1)))
      (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) (Type (u + 1))) :=
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u, u, u + 1}
    (polynomialTowerFirst A B C) _ _

/-- `g₂ : Sh(C_{C/B/A}) ⟶ Sh(C_{C/A})`, the morphism of topoi induced by `u₂`. -/
def polynomialTowerSecondTopos :
    MorphismOfTopoi (Sheaf (polynomialTowerTopology A B C) (Type (u + 1)))
      (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) (Type (u + 1))) :=
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u, u, u + 1}
    (polynomialTowerSecond A B C) _ _

/-- `g₃ : Sh(C_{C/B/A}) ⟶ Sh(C_{C/B})`, the morphism of topoi induced by `u₃`. -/
def polynomialTowerThirdTopos :
    MorphismOfTopoi (Sheaf (polynomialTowerTopology A B C) (Type (u + 1)))
      (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) (Type (u + 1))) :=
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u, u, u + 1}
    (polynomialTowerThird A B C) _ _

/-- The inverse image of `g₁` is restriction along `u₁`. -/
theorem polynomialTowerFirstTopos_inverseImage :
    (polynomialTowerFirstTopos A B C).inverseImage =
      (polynomialTowerFirst A B C).sheafPushforwardContinuous (Type (u + 1))
        (polynomialTowerTopology A B C) (polynomialTopology A (towerBaseAlgebra A B)) := rfl

/-- The inverse image of `g₂` is restriction along `u₂`. -/
theorem polynomialTowerSecondTopos_inverseImage :
    (polynomialTowerSecondTopos A B C).inverseImage =
      (polynomialTowerSecond A B C).sheafPushforwardContinuous (Type (u + 1))
        (polynomialTowerTopology A B C) (polynomialTopology A (towerTotalAlgebra A C)) := rfl

/-- The inverse image of `g₃` is restriction along `u₃`. -/
theorem polynomialTowerThirdTopos_inverseImage :
    (polynomialTowerThirdTopos A B C).inverseImage =
      (polynomialTowerThird A B C).sheafPushforwardContinuous (Type (u + 1))
        (polynomialTowerTopology A B C) (polynomialTopology B (towerRelativeAlgebra B C)) := rfl

/-! ### The three morphisms of ringed topoi -/

/-- `𝒪₁ = g₁⁻¹𝒪`: the inverse image along `g₁` of the tautological sheaf of rings on
`C_{B/A}`. -/
@[stacks 08QT "the sheaf 𝒪₁ = g₁⁻¹𝒪"]
def polynomialTowerFirstStructureSheaf :
    Sheaf (polynomialTowerTopology A B C) CommRingCat.{u + 1} :=
  (polynomialTowerFirstTopos A B C).inverseImageRing.obj
    (polynomialStructureSheaf A (towerBaseAlgebra A B))

/-- `𝒪₂ = g₂⁻¹𝒪`: the inverse image along `g₂` of the tautological sheaf of rings on
`C_{C/A}`. -/
@[stacks 08QT "the sheaf 𝒪₂ = g₂⁻¹𝒪"]
def polynomialTowerSecondStructureSheaf :
    Sheaf (polynomialTowerTopology A B C) CommRingCat.{u + 1} :=
  (polynomialTowerSecondTopos A B C).inverseImageRing.obj
    (polynomialStructureSheaf A (towerTotalAlgebra A C))

/-- `𝒪₃ = g₃⁻¹𝒪`: the inverse image along `g₃` of the tautological sheaf of rings on
`C_{C/B}`. -/
@[stacks 08QT "the sheaf 𝒪₃ = g₃⁻¹𝒪"]
def polynomialTowerThirdStructureSheaf :
    Sheaf (polynomialTowerTopology A B C) CommRingCat.{u + 1} :=
  (polynomialTowerThirdTopos A B C).inverseImageRing.obj
    (polynomialStructureSheaf B (towerRelativeAlgebra B C))

/-- The ringed topos `(Sh(C_{C/B/A}), 𝒪₁)`. -/
def polynomialTowerFirstRingedTopos : AlgebraicGeometry.RingedTopos.{u, u + 1, u + 1} where
  C := polynomialTowerSite A B C
  J := polynomialTowerTopology A B C
  O := polynomialTowerFirstStructureSheaf A B C

/-- The ringed topos `(Sh(C_{C/B/A}), 𝒪₂)`. -/
def polynomialTowerSecondRingedTopos : AlgebraicGeometry.RingedTopos.{u, u + 1, u + 1} where
  C := polynomialTowerSite A B C
  J := polynomialTowerTopology A B C
  O := polynomialTowerSecondStructureSheaf A B C

/-- The ringed topos `(Sh(C_{C/B/A}), 𝒪₃)`. -/
def polynomialTowerThirdRingedTopos : AlgebraicGeometry.RingedTopos.{u, u + 1, u + 1} where
  C := polynomialTowerSite A B C
  J := polynomialTowerTopology A B C
  O := polynomialTowerThirdStructureSheaf A B C

/-- `g₁ : (Sh(C_{C/B/A}), 𝒪₁) ⟶ (Sh(C_{B/A}), 𝒪)`, the first morphism of ringed topoi of the
fundamental triangle. Its structure map is the unit of `g₁⁻¹ ⊣ g₁_*` on sheaves of commutative
rings at `𝒪`, which is the structure map that `𝒪₁ = g₁⁻¹𝒪` forces. -/
@[stacks 08QT "the morphism g₁ of ringed topoi"]
def polynomialTowerFirstRinged :
    AlgebraicGeometry.RingedToposHom (polynomialTowerFirstRingedTopos A B C)
      (polynomialStructureRingedTopos A (towerBaseAlgebra A B)) where
  toToposHom := polynomialTowerFirstTopos A B C
  fSharp := (polynomialTowerFirstTopos A B C).ringAdjunction.unit.app
    (polynomialStructureSheaf A (towerBaseAlgebra A B))

/-- `g₂ : (Sh(C_{C/B/A}), 𝒪₂) ⟶ (Sh(C_{C/A}), 𝒪)`, the second morphism of ringed topoi of the
fundamental triangle. -/
@[stacks 08QT "the morphism g₂ of ringed topoi"]
def polynomialTowerSecondRinged :
    AlgebraicGeometry.RingedToposHom (polynomialTowerSecondRingedTopos A B C)
      (polynomialStructureRingedTopos A (towerTotalAlgebra A C)) where
  toToposHom := polynomialTowerSecondTopos A B C
  fSharp := (polynomialTowerSecondTopos A B C).ringAdjunction.unit.app
    (polynomialStructureSheaf A (towerTotalAlgebra A C))

/-- `g₃ : (Sh(C_{C/B/A}), 𝒪₃) ⟶ (Sh(C_{C/B}), 𝒪)`, the third morphism of ringed topoi of the
fundamental triangle. -/
@[stacks 08QT "the morphism g₃ of ringed topoi"]
def polynomialTowerThirdRinged :
    AlgebraicGeometry.RingedToposHom (polynomialTowerThirdRingedTopos A B C)
      (polynomialStructureRingedTopos B (towerRelativeAlgebra B C)) where
  toToposHom := polynomialTowerThirdTopos A B C
  fSharp := (polynomialTowerThirdTopos A B C).ringAdjunction.unit.app
    (polynomialStructureSheaf B (towerRelativeAlgebra B C))

/-- The geometric morphism underlying `g₁` is the morphism of topoi induced by `u₁`. -/
theorem polynomialTowerFirstRinged_toToposHom :
    (polynomialTowerFirstRinged A B C).toToposHom = polynomialTowerFirstTopos A B C := rfl

/-- The geometric morphism underlying `g₂` is the morphism of topoi induced by `u₂`. -/
theorem polynomialTowerSecondRinged_toToposHom :
    (polynomialTowerSecondRinged A B C).toToposHom = polynomialTowerSecondTopos A B C := rfl

/-- The geometric morphism underlying `g₃` is the morphism of topoi induced by `u₃`. -/
theorem polynomialTowerThirdRinged_toToposHom :
    (polynomialTowerThirdRinged A B C).toToposHom = polynomialTowerThirdTopos A B C := rfl

/-- The structure sheaf of the source of `g₁` is `g₁⁻¹𝒪`. -/
theorem polynomialTowerFirstRingedTopos_O :
    (polynomialTowerFirstRingedTopos A B C).O =
      (polynomialTowerFirstTopos A B C).inverseImageRing.obj
        (polynomialStructureRingedTopos A (towerBaseAlgebra A B)).O := rfl

/-- The structure sheaf of the source of `g₂` is `g₂⁻¹𝒪`. -/
theorem polynomialTowerSecondRingedTopos_O :
    (polynomialTowerSecondRingedTopos A B C).O =
      (polynomialTowerSecondTopos A B C).inverseImageRing.obj
        (polynomialStructureRingedTopos A (towerTotalAlgebra A C)).O := rfl

/-- The structure sheaf of the source of `g₃` is `g₃⁻¹𝒪`. -/
theorem polynomialTowerThirdRingedTopos_O :
    (polynomialTowerThirdRingedTopos A B C).O =
      (polynomialTowerThirdTopos A B C).inverseImageRing.obj
        (polynomialStructureRingedTopos B (towerRelativeAlgebra B C)).O := rfl

/-! ### The projections to the point -/

/-- `π : Sh(C_{C/B/A}) ⟶ Sh(*)`, the projection of the chaotic site `C_{C/B/A}` to the
point. -/
@[stacks 08QT "the projection π"]
abbrev polynomialTowerProjection :=
  (polynomialTowerRingedPoint A B C).fibredSituation.projection

/-- `π₁ : Sh(C_{B/A}) ⟶ Sh(*)`. -/
abbrev polynomialTowerFirstProjection :=
  (polynomialRingedPoint A (towerBaseAlgebra A B)).fibredSituation.projection

/-- `π₂ : Sh(C_{C/A}) ⟶ Sh(*)`. -/
abbrev polynomialTowerSecondProjection :=
  (polynomialRingedPoint A (towerTotalAlgebra A C)).fibredSituation.projection

/-- `π₃ : Sh(C_{C/B}) ⟶ Sh(*)`. -/
abbrev polynomialTowerThirdProjection :=
  (polynomialRingedPoint B (towerRelativeAlgebra B C)).fibredSituation.projection

/-- `π = π₁ ∘ g₁`, on inverse images: both are restriction along the unique functor to the
point, because `u₁` followed by `C_{B/A} ⥤ *` is `C_{C/B/A} ⥤ *`. -/
@[stacks 08QT "π = π₁ ∘ g₁, on inverse images"]
theorem polynomialTowerFirstProjection_comp_inverseImage :
    ((polynomialTowerFirstProjection A B).comp
        (polynomialTowerFirstTopos A B C)).inverseImage =
      (polynomialTowerProjection A B C).inverseImage := rfl

/-- `π = π₂ ∘ g₂`, on inverse images. -/
@[stacks 08QT "π = π₂ ∘ g₂, on inverse images"]
theorem polynomialTowerSecondProjection_comp_inverseImage :
    ((polynomialTowerSecondProjection A C).comp
        (polynomialTowerSecondTopos A B C)).inverseImage =
      (polynomialTowerProjection A B C).inverseImage := rfl

/-- `π = π₃ ∘ g₃`, on inverse images. -/
@[stacks 08QT "π = π₃ ∘ g₃, on inverse images"]
theorem polynomialTowerThirdProjection_comp_inverseImage :
    ((polynomialTowerThirdProjection B C).comp
        (polynomialTowerThirdTopos A B C)).inverseImage =
      (polynomialTowerProjection A B C).inverseImage := rfl

/-- `π = π₁ ∘ g₁`, on direct images: the canonical isomorphism `(π₁ ∘ g₁)_* ≅ π_*` between the
two right adjoints of the common inverse image. -/
@[stacks 08QT "π = π₁ ∘ g₁, on direct images"]
def polynomialTowerFirstProjection_comp_pushforwardIso :
    ((polynomialTowerFirstProjection A B).comp (polynomialTowerFirstTopos A B C)).pushforward ≅
      (polynomialTowerProjection A B C).pushforward :=
  (((polynomialTowerFirstProjection A B).comp
          (polynomialTowerFirstTopos A B C)).adj.ofNatIsoLeft
      (eqToIso (polynomialTowerFirstProjection_comp_inverseImage A B C))).rightAdjointUniq
    (polynomialTowerProjection A B C).adj

/-- `π = π₂ ∘ g₂`, on direct images. -/
@[stacks 08QT "π = π₂ ∘ g₂, on direct images"]
def polynomialTowerSecondProjection_comp_pushforwardIso :
    ((polynomialTowerSecondProjection A C).comp (polynomialTowerSecondTopos A B C)).pushforward ≅
      (polynomialTowerProjection A B C).pushforward :=
  (((polynomialTowerSecondProjection A C).comp
          (polynomialTowerSecondTopos A B C)).adj.ofNatIsoLeft
      (eqToIso (polynomialTowerSecondProjection_comp_inverseImage A B C))).rightAdjointUniq
    (polynomialTowerProjection A B C).adj

/-- `π = π₃ ∘ g₃`, on direct images. -/
@[stacks 08QT "π = π₃ ∘ g₃, on direct images"]
def polynomialTowerThirdProjection_comp_pushforwardIso :
    ((polynomialTowerThirdProjection B C).comp (polynomialTowerThirdTopos A B C)).pushforward ≅
      (polynomialTowerProjection A B C).pushforward :=
  (((polynomialTowerThirdProjection B C).comp
          (polynomialTowerThirdTopos A B C)).adj.ofNatIsoLeft
      (eqToIso (polynomialTowerThirdProjection_comp_inverseImage A B C))).rightAdjointUniq
    (polynomialTowerProjection A B C).adj

end CommAlgCat

end
