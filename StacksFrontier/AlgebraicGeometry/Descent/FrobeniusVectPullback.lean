module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVect
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import StacksFrontier.RingTheory.MilnorPatching.OneGeneratorFrobenius

/-!
# Frobenius and the one-generator square on vector bundles

Let `p` be a prime. This file records two compatibilities of restriction of vector bundles,
both instances of the pseudofunctoriality of pullback: a commuting square of schemes gives a
canonical isomorphism between the two resulting double restrictions, on all sheaves of modules
and on the finite locally free ones.

The first instance is Frobenius-equivariance: for a morphism `g : X ⟶ Y` of schemes in
characteristic `p` the absolute Frobenius is natural
(`Stacks.Frobenius.absoluteFrobenius_naturality`), so `g ≫ F_Y = F_X ≫ g` and the two ways of
restricting a vector bundle on `Y` to `X` after one Frobenius pullback agree.

The second concerns the affine square of Stacks Example 0EVG

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

whose spectra form the one-generator almost blowup square: the modification is
`Spec (A ⧸ J)`, the centre is `Spec (A ⧸ fA)` and the exceptional corner is
`Spec (A ⧸ (J + fA))`. The square commutes because both composites `A ⟶ A ⧸ (J + fA)` are
the quotient map, and that one equality produces the canonical comparison between the two
double restrictions of a vector bundle from `Spec A` to the exceptional corner.

## Main definitions

* `AlgebraicGeometry.modulesPullbackSquareIso` and
  `AlgebraicGeometry.vectPullbackSquareIso`: the canonical comparison of the two double
  restrictions attached to a commuting square of schemes.
* `AlgebraicGeometry.OneGeneratorSquare.toMod`,
  `AlgebraicGeometry.OneGeneratorSquare.toCtr`,
  `AlgebraicGeometry.OneGeneratorSquare.modToExc` and
  `AlgebraicGeometry.OneGeneratorSquare.ctrToExc`: the four ring maps of the square.
* `AlgebraicGeometry.OneGeneratorSquare.squareModulesIso` and
  `AlgebraicGeometry.OneGeneratorSquare.squareVectIso`: the canonical comparison of the two
  double restrictions to the exceptional corner.
* `AlgebraicGeometry.OneGeneratorSquare.charBase`,
  `AlgebraicGeometry.OneGeneratorSquare.charMod`,
  `AlgebraicGeometry.OneGeneratorSquare.charCtr` and
  `AlgebraicGeometry.OneGeneratorSquare.charExc`: the four corners are in characteristic `p`
  as soon as `A` is.

## Main results

* `AlgebraicGeometry.frobeniusModulesPullbackIso_eq_modulesPullbackSquareIso` and
  `AlgebraicGeometry.frobeniusVectPullbackIso_eq_vectPullbackSquareIso`: the Frobenius
  comparisons `AlgebraicGeometry.frobeniusModulesPullbackIso` and
  `AlgebraicGeometry.frobeniusVectPullbackIso` are the comparisons of the Frobenius naturality
  square.
* `AlgebraicGeometry.OneGeneratorSquare.toMod_comp_modToExc`: the square of ring maps
  commutes.
* `AlgebraicGeometry.OneGeneratorSquare.specMap_square`: the square of affine schemes
  commutes.
* `AlgebraicGeometry.OneGeneratorSquare.natCast_quotient_eq_zero`: a prime vanishing in `A`
  vanishes in every quotient of `A`.

## Implementation notes

Every isomorphism of functors between categories of vector bundles here is assembled from the
corresponding isomorphism on sheaves of modules by `CategoryTheory.NatIso.ofComponents` and
`CategoryTheory.ObjectProperty.isoMk`, which is possible because
`AlgebraicGeometry.Scheme.Vect.pullback` is a `CategoryTheory.ObjectProperty.lift` of
`AlgebraicGeometry.Scheme.Modules.pullback`; the components on underlying modules are
therefore `rfl`, which is what the `simp` lemmas record. Both the Frobenius comparison and the
comparison for the one-generator square are instances of the same construction for an
arbitrary commuting square.

The four ring maps are `CommRingCat` wrappers; the two surjections out of `A ⧸ J` and `A ⧸ fA`
are `MilnorPatching.OneGeneratorFrobenius.toBase` and
`MilnorPatching.OneGeneratorFrobenius.surjection`.

## References

* [Stacks Project, Tag 0CC7](https://stacks.math.columbia.edu/tag/0CC7)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Restriction along a commuting square of schemes -/

section Square

variable {W X Y Z : Scheme.{u}} {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}

/-- **The canonical comparison of the two double restrictions attached to a commuting square
of schemes, on all sheaves of modules.** Given `a ≫ b = c ≫ d`, restricting along `b` and then
along `a` agrees with restricting along `d` and then along `c`, because pullback is
pseudofunctorial. -/
noncomputable def modulesPullbackSquareIso (h : a ≫ b = c ≫ d) :
    Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback d ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp c d).symm

/-- **The canonical comparison of the two double restrictions of a vector bundle attached to a
commuting square of schemes.** This is `AlgebraicGeometry.modulesPullbackSquareIso`
transported to the full subcategories of finite locally free modules. -/
noncomputable def vectPullbackSquareIso (h : a ≫ b = c ≫ d) :
    Scheme.Vect.pullback b ⋙ Scheme.Vect.pullback a ≅
      Scheme.Vect.pullback d ⋙ Scheme.Vect.pullback c :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((modulesPullbackSquareIso h).app M.obj))
    (fun {_ _} φ ↦ ObjectProperty.hom_ext _ ((modulesPullbackSquareIso h).hom.naturality φ.hom))

/-- The comparison of `AlgebraicGeometry.vectPullbackSquareIso` is the one of
`AlgebraicGeometry.modulesPullbackSquareIso` on underlying sheaves of modules. -/
@[simp]
lemma vectPullbackSquareIso_hom_app_hom (h : a ≫ b = c ≫ d) (M : X.Vect) :
    ((vectPullbackSquareIso h).hom.app M).hom = (modulesPullbackSquareIso h).hom.app M.obj :=
  rfl

/-- The inverse comparison of `AlgebraicGeometry.vectPullbackSquareIso` is the one of
`AlgebraicGeometry.modulesPullbackSquareIso` on underlying sheaves of modules. -/
@[simp]
lemma vectPullbackSquareIso_inv_app_hom (h : a ≫ b = c ≫ d) (M : X.Vect) :
    ((vectPullbackSquareIso h).inv.app M).hom = (modulesPullbackSquareIso h).inv.app M.obj :=
  rfl

end Square

/-! ### Frobenius pullback commutes with restriction -/

variable {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  (hY : IsInCharacteristic Y p) (g : X ⟶ Y)

/-- **The Frobenius comparison on all sheaves of modules is the comparison of the Frobenius
naturality square.** `AlgebraicGeometry.frobeniusModulesPullbackIso` is
`AlgebraicGeometry.modulesPullbackSquareIso` for the commuting square
`g ≫ F_Y = F_X ≫ g` of `Stacks.Frobenius.absoluteFrobenius_naturality`. -/
lemma frobeniusModulesPullbackIso_eq_modulesPullbackSquareIso :
    frobeniusModulesPullbackIso g p hX hY =
      modulesPullbackSquareIso (absoluteFrobenius_naturality g p hX hY).symm :=
  rfl

/-- **The Frobenius comparison of vector bundles is the comparison of the Frobenius naturality
square.** `AlgebraicGeometry.frobeniusVectPullbackIso` is
`AlgebraicGeometry.vectPullbackSquareIso` for the commuting square `g ≫ F_Y = F_X ≫ g` of
`Stacks.Frobenius.absoluteFrobenius_naturality`. -/
lemma frobeniusVectPullbackIso_eq_vectPullbackSquareIso :
    frobeniusVectPullbackIso g p hX hY =
      vectPullbackSquareIso (absoluteFrobenius_naturality g p hX hY).symm :=
  rfl

/-- The comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` is the one of
`AlgebraicGeometry.frobeniusModulesPullbackIso` on underlying sheaves of modules. -/
@[simp]
lemma frobeniusVectPullbackIso_hom_app_hom (M : Y.Vect) :
    ((frobeniusVectPullbackIso g p hX hY).hom.app M).hom =
      (frobeniusModulesPullbackIso g p hX hY).hom.app M.obj :=
  rfl

/-- The inverse comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` is the one of
`AlgebraicGeometry.frobeniusModulesPullbackIso` on underlying sheaves of modules. -/
@[simp]
lemma frobeniusVectPullbackIso_inv_app_hom (M : Y.Vect) :
    ((frobeniusVectPullbackIso g p hX hY).inv.app M).hom =
      (frobeniusModulesPullbackIso g p hX hY).inv.app M.obj :=
  rfl

/-! ### The one-generator square -/

namespace OneGeneratorSquare

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A)

/-- The quotient map `A ⟶ A ⧸ J` onto the coordinate ring of the modification. -/
noncomputable def toMod : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ J) :=
  CommRingCat.ofHom (Ideal.Quotient.mk J)

/-- The quotient map `A ⟶ A ⧸ fA` onto the coordinate ring of the centre. -/
noncomputable def toCtr : CommRingCat.of A ⟶ CommRingCat.of (A ⧸ Ideal.span {f}) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))

/-- The surjection `A ⧸ J ⟶ A ⧸ (J + fA)` from the modification onto the exceptional corner,
namely `MilnorPatching.OneGeneratorFrobenius.toBase` read in `CommRingCat`. -/
noncomputable def modToExc :
    CommRingCat.of (A ⧸ J) ⟶ CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})) :=
  CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.toBase f J)

/-- The surjection `A ⧸ fA ⟶ A ⧸ (J + fA)` from the centre onto the exceptional corner,
namely `MilnorPatching.OneGeneratorFrobenius.surjection` read in `CommRingCat`. -/
noncomputable def ctrToExc :
    CommRingCat.of (A ⧸ Ideal.span {f}) ⟶ CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})) :=
  CommRingCat.ofHom (MilnorPatching.OneGeneratorFrobenius.surjection f J)

/-- **The square of ring maps commutes.** Both composites `A ⟶ A ⧸ (J + fA)` are the quotient
map, because `MilnorPatching.OneGeneratorFrobenius.toBase` and
`MilnorPatching.OneGeneratorFrobenius.surjection` are the identity on representatives. -/
theorem toMod_comp_modToExc : toMod A J ≫ modToExc A f J = toCtr A f ≫ ctrToExc A f J := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change MilnorPatching.OneGeneratorFrobenius.toBase f J (Ideal.Quotient.mk J x) =
    MilnorPatching.OneGeneratorFrobenius.surjection f J (Ideal.Quotient.mk (Ideal.span {f}) x)
  rw [MilnorPatching.OneGeneratorFrobenius.toBase_mk,
    MilnorPatching.OneGeneratorFrobenius.surjection_mk]

/-- **The square of affine schemes commutes.** This is `Spec` applied to
`AlgebraicGeometry.OneGeneratorSquare.toMod_comp_modToExc`; `Spec.map` is contravariant, so
the composite through the modification is `Spec.map (modToExc …) ≫ Spec.map (toMod …)`. -/
theorem specMap_square :
    Spec.map (modToExc A f J) ≫ Spec.map (toMod A J) =
      Spec.map (ctrToExc A f J) ≫ Spec.map (toCtr A f) := by
  rw [← Spec.map_comp, ← Spec.map_comp, toMod_comp_modToExc]

/-- **The canonical comparison of the two double restrictions to the exceptional corner, on
all sheaves of modules**, the instance of `AlgebraicGeometry.modulesPullbackSquareIso` for the
commuting square `AlgebraicGeometry.OneGeneratorSquare.specMap_square`. -/
noncomputable def squareModulesIso :
    Scheme.Modules.pullback (Spec.map (toMod A J)) ⋙
        Scheme.Modules.pullback (Spec.map (modToExc A f J)) ≅
      Scheme.Modules.pullback (Spec.map (toCtr A f)) ⋙
        Scheme.Modules.pullback (Spec.map (ctrToExc A f J)) :=
  modulesPullbackSquareIso (specMap_square A f J)

/-- **The canonical comparison of the two double restrictions of a vector bundle to the
exceptional corner**, the instance of `AlgebraicGeometry.vectPullbackSquareIso` for the
commuting square `AlgebraicGeometry.OneGeneratorSquare.specMap_square`. -/
noncomputable def squareVectIso :
    Scheme.Vect.pullback (Spec.map (toMod A J)) ⋙
        Scheme.Vect.pullback (Spec.map (modToExc A f J)) ≅
      Scheme.Vect.pullback (Spec.map (toCtr A f)) ⋙
        Scheme.Vect.pullback (Spec.map (ctrToExc A f J)) :=
  vectPullbackSquareIso (specMap_square A f J)

/-- The comparison of `AlgebraicGeometry.OneGeneratorSquare.squareVectIso` is the one of
`AlgebraicGeometry.OneGeneratorSquare.squareModulesIso` on underlying sheaves of modules. -/
@[simp]
lemma squareVectIso_hom_app_hom (M : (Spec (.of A)).Vect) :
    ((squareVectIso A f J).hom.app M).hom = (squareModulesIso A f J).hom.app M.obj :=
  vectPullbackSquareIso_hom_app_hom _ M

/-- The inverse comparison of `AlgebraicGeometry.OneGeneratorSquare.squareVectIso` is the one
of `AlgebraicGeometry.OneGeneratorSquare.squareModulesIso` on underlying sheaves of
modules. -/
@[simp]
lemma squareVectIso_inv_app_hom (M : (Spec (.of A)).Vect) :
    ((squareVectIso A f J).inv.app M).hom = (squareModulesIso A f J).inv.app M.obj :=
  vectPullbackSquareIso_inv_app_hom _ M

/-! ### The four corners are in characteristic `p` -/

/-- **A prime vanishing in `A` vanishes in every quotient of `A`.** -/
theorem natCast_quotient_eq_zero (p : ℕ) (hp : (p : A) = 0) (𝔞 : Ideal A) :
    (p : A ⧸ 𝔞) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk 𝔞), hp, map_zero]

variable (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)

/-- `Spec A` is in characteristic `p`. -/
noncomputable abbrev charBase : IsInCharacteristic (Spec (.of A)) p :=
  isInCharacteristic_spec A p hp

/-- The modification `Spec (A ⧸ J)` is in characteristic `p`. -/
noncomputable abbrev charMod : IsInCharacteristic (Spec (.of (A ⧸ J))) p :=
  isInCharacteristic_spec (A ⧸ J) p (natCast_quotient_eq_zero A p hp J)

/-- The centre `Spec (A ⧸ fA)` is in characteristic `p`. -/
noncomputable abbrev charCtr : IsInCharacteristic (Spec (.of (A ⧸ Ideal.span {f}))) p :=
  isInCharacteristic_spec (A ⧸ Ideal.span {f}) p
    (natCast_quotient_eq_zero A p hp (Ideal.span {f}))

/-- The exceptional corner `Spec (A ⧸ (J + fA))` is in characteristic `p`. -/
noncomputable abbrev charExc :
    IsInCharacteristic (Spec (.of (A ⧸ (J ⊔ Ideal.span {f})))) p :=
  isInCharacteristic_spec (A ⧸ (J ⊔ Ideal.span {f})) p
    (natCast_quotient_eq_zero A p hp (J ⊔ Ideal.span {f}))

end OneGeneratorSquare

end AlgebraicGeometry

end
