module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Stability

/-!
# Stalks of affine schemes and transport of stalk maps

This file collects the facts about stalks that a deformation-theoretic argument about local
rings of schemes needs. First, for a local ring `A` the stalk of `Spec A` at the closed point
is `A` itself, and that identification is the canonical map to the stalk. Second, the stalk of
a scheme flat over an affine base is a flat algebra over the coordinate ring of that base.
Finally there is a group of transport lemmas: a stalk depends on a point, so an equality of
points produces an `eqToHom` between stalks, and composing a stalk map with such an `eqToHom`
is again a stalk map — of a composite morphism, or of a morphism between different points.

## Main definitions

* `Deformation.Examples.localStalkRingEquiv`: the identification of a local ring with the
  stalk of its spectrum at the closed point.

## Main results

* `Deformation.Examples.localStalkRingEquiv_apply`: that identification is the canonical map
  to the stalk.
* `Deformation.Examples.flat_stalk_algebra_of_flat`: the stalk of a scheme flat over `Spec R`
  is flat over `R`.
* `Deformation.Examples.arrowStalkMapIso_left_germ`: the affine comparison of a stalk map with
  a map of localizations sends a germ of a global section to the image of that section.
* `Deformation.Examples.stalkMap_comp_transport` and
  `Deformation.Examples.stalkMap_of_comp_eq`: the stalk map of a composite, written through
  the transports along the induced equalities of points.
* `Deformation.Examples.stalkBaseMap_natural`: naturality of the map from the coordinate ring
  of an affine base to the stalk of a scheme over it.

## Implementation notes

The transport lemmas are stated with the `eqToHom` on the side the stalk map leaves it on, so
that they can be rewritten with directly. They are proved by `cases` on the equality of
points; the proofs then have to identify two proofs of the same equality of points, which is
`Subsingleton.elim` in a `Prop`.

## References

* [Stacks Project, Tag 0DZM](https://stacks.math.columbia.edu/tag/0DZM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

/-- For a local ring `A`, the identification of `A` with the stalk of the structure sheaf of
`Spec A` at the closed point: the complement of the maximal ideal consists of units, so the
localization there is `A` itself. -/
noncomputable def localStalkRingEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : PrimeSpectrum A) (hp : p.asIdeal = IsLocalRing.maximalIdeal A) :
    A ≃+* (Spec (.of A)).presheaf.stalk p := by
  letI : Algebra A ((Spec (.of A)).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra A p
  have hM : p.asIdeal.primeCompl = IsUnit.submonoid A := by
    ext a
    change a ∉ p.asIdeal ↔ IsUnit a
    rw [hp, IsLocalRing.mem_maximalIdeal]
    simp [mem_nonunits_iff]
  let e₁ : A ≃ₐ[A] Localization.AtPrime p.asIdeal :=
    IsLocalization.atUnits A p.asIdeal.primeCompl (by rw [hM])
  exact e₁.toRingEquiv.trans (StructureSheaf.stalkIso A p).toRingEquiv

/-- The identification `localStalkRingEquiv` is the canonical map from a ring to the stalk of
its spectrum. -/
theorem localStalkRingEquiv_apply
    {A : Type u} [CommRing A] [IsLocalRing A]
    (p : PrimeSpectrum A) (hp : p.asIdeal = IsLocalRing.maximalIdeal A)
    (a : A) :
    localStalkRingEquiv p hp a = (StructureSheaf.toStalk A p).hom a := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk p) :=
    StructureSheaf.stalkAlgebra A p
  have hM : p.asIdeal.primeCompl = IsUnit.submonoid A := by
    ext b
    show b ∉ p.asIdeal ↔ IsUnit b
    rw [hp, IsLocalRing.mem_maximalIdeal]
    simp [mem_nonunits_iff]
  show (StructureSheaf.stalkIso A p)
    ((IsLocalization.atUnits A p.asIdeal.primeCompl hM.le).toRingEquiv a) = _
  have hUnit : (IsLocalization.atUnits A p.asIdeal.primeCompl hM.le).toRingEquiv a =
      algebraMap A (Localization.AtPrime p.asIdeal) a := by
    simpa using (IsLocalization.atUnits A p.asIdeal.primeCompl hM.le).commutes a
  rw [hUnit]
  exact (StructureSheaf.stalkIso A p).commutes a

/-- The stalk of a scheme flat over `Spec R` is a flat `R`-algebra: it is flat over the stalk
of `Spec R` at the image point, which in turn is a localization of `R`. -/
theorem flat_stalk_algebra_of_flat {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [Flat f] (y : Y) :
    letI : Algebra R ((Spec (.of R)).presheaf.stalk (f.base y)) :=
      StructureSheaf.stalkAlgebra R (f.base y)
    letI : Algebra R (Y.presheaf.stalk y) :=
      ((f.stalkMap y).hom.comp
        (algebraMap R ((Spec (.of R)).presheaf.stalk (f.base y)))).toAlgebra
    Module.Flat R (Y.presheaf.stalk y) := by
  let U := (Spec (.of R)).presheaf.stalk (f.base y)
  let T := Y.presheaf.stalk y
  let : Algebra R U := StructureSheaf.stalkAlgebra R (f.base y)
  let : Algebra U T := (f.stalkMap y).hom.toAlgebra
  let : Algebra R T := ((f.stalkMap y).hom.comp (algebraMap R U)).toAlgebra
  have : IsScalarTower R U T := .of_algebraMap_eq' rfl
  have : (f.base y).asIdeal.IsPrime := (f.base y).isPrime
  have : IsLocalization.AtPrime U (f.base y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R (f.base y)
  have : Module.Flat R U := IsLocalization.flat U (f.base y).asIdeal.primeCompl
  have : Module.Flat U T := by
    rw [← RingHom.flat_algebraMap_iff]
    exact Flat.stalkMap f y
  exact Module.Flat.trans R U T

/-- Under the affine comparison of a stalk map with the induced map of localizations, the germ
at `f x` of a section over the affine open `U` is the image of that section in the
localization. -/
theorem arrowStalkMapIso_left_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) (a : Γ(Y, U)) :
    let i := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx
    i.hom.left.hom (Y.presheaf.germ U (f x) (hVU hx) a) =
      algebraMap Γ(Y, U)
        (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal) a := by
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hx⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hx⟩
  exact (IsLocalization.algEquiv
      (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal.primeCompl
      (Y.presheaf.stalk (f x))
      (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)).commutes a

/-- Transporting the germ of a global section along an equality of points gives the germ at the
other point. -/
theorem germ_top_transport {Y : Scheme.{u}} {p q : Y} (h : p = q)
    (a : Γ(Y, ⊤)) :
    (eqToHom (congrArg (fun t : Y => Y.presheaf.stalk t) h)).hom
      (Y.presheaf.germ ⊤ p trivial a) = Y.presheaf.germ ⊤ q trivial a := by
  cases h
  rfl

/-- Transporting the canonical image of a ring element in a stalk of its spectrum along an
equality of points gives the canonical image at the other point. -/
theorem toStalk_transport {R : Type u} [CommRing R]
    {p q : PrimeSpectrum R} (h : p = q) (a : R) :
    (eqToHom (congrArg (fun t : PrimeSpectrum R =>
      (Spec (.of R)).presheaf.stalk t) h)).hom
      ((StructureSheaf.toStalk R p).hom a) =
        (StructureSheaf.toStalk R q).hom a := by
  cases h
  rfl

/-- The stalk map of a composite, with the `eqToHom` between the two descriptions of the image
point on the right. -/
private theorem stalkMap_comp_eqToHom {A B C : Scheme.{u}} (i : A ⟶ B) (j : B ⟶ C) (x : A)
    (hp : j (i x) = (i ≫ j) x) :
    ((i ≫ j).stalkMap x).hom =
      (i.stalkMap x).hom.comp
        ((j.stalkMap (i x)).hom.comp (eqToHom (congrArg C.presheaf.stalk hp.symm)).hom) := by
  have hc : (eqToHom (congrArg C.presheaf.stalk hp.symm)).hom = RingHom.id _ := by
    rw [Subsingleton.elim hp (rfl : j (i x) = (i ≫ j) x)]
    rfl
  rw [hc]
  ext a
  simp only [Scheme.Hom.stalkMap_comp, RingHom.comp_apply]
  rfl

/-- The stalk map of a composite, written through the transports along the equalities of points
that the two factors induce. -/
theorem stalkMap_comp_transport
    {Y Z W : Scheme.{u}} (f : Z ⟶ Y) (g : W ⟶ Z)
    (w : W) (z : Z) (y : Y)
    (hw : g w = z) (hz : f z = y) (hy : (g ≫ f) w = y) :
    ((g ≫ f).stalkMap w).hom.comp
        (eqToHom (congrArg Y.presheaf.stalk hy.symm)).hom =
      ((g.stalkMap w).hom.comp
        (eqToHom (congrArg Z.presheaf.stalk hw.symm)).hom).comp
        ((f.stalkMap z).hom.comp
          (eqToHom (congrArg Y.presheaf.stalk hz.symm)).hom) := by
  simp only [Scheme.Hom.comp_apply] at hy ⊢
  cases hw
  cases hz
  cases hy
  rw [stalkMap_comp_eqToHom g f w rfl]
  rfl

/-- The stalk map of a morphism that factors as `i ≫ j`, written through the transport along the
equality of points the factorisation induces. -/
theorem stalkMap_of_comp_eq
    {A B C : Scheme.{u}} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (h : i ≫ j = k) (x : A) (hp : j (i x) = k x) :
    (k.stalkMap x).hom =
      (i.stalkMap x).hom.comp
        ((j.stalkMap (i x)).hom.comp
          (eqToHom (congrArg C.presheaf.stalk hp.symm)).hom) := by
  cases h
  exact stalkMap_comp_eqToHom i j x hp

/-- Naturality of the map from the coordinate ring of an affine base to the stalk of a scheme
over it: a commuting square of schemes over a map of base rings induces a commuting square of
maps into stalks. -/
theorem stalkBaseMap_natural
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) (p : Z ⟶ Spec (.of R)) (q : Y ⟶ Spec (.of S))
    (hw : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom g)) (y : Y) :
    StructureSheaf.toStalk R (p (f y)) ≫ p.stalkMap (f y) ≫ f.stalkMap y =
      CommRingCat.ofHom g ≫ StructureSheaf.toStalk S (q y) ≫ q.stalkMap y := by
  have hh : StructureSheaf.toStalk R ((f ≫ p) y) ≫ (f ≫ p).stalkMap y =
      StructureSheaf.toStalk R ((q ≫ Spec.map (CommRingCat.ofHom g)) y) ≫
        (q ≫ Spec.map (CommRingCat.ofHom g)).stalkMap y := by rw [hw]
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hh
  have he := congrArg (fun t : CommRingCat.of R ⟶
      (Spec (.of S)).presheaf.stalk (q y) => t ≫ q.stalkMap y)
    (stalkMap_toStalk (CommRingCat.ofHom g) (q y))
  exact hh.trans (he.trans (Category.assoc _ _ _))

/-- Transporting the map from the coordinate ring of an affine base into a stalk along an
equality of points gives the corresponding map at the other point. -/
theorem stalkBaseMap_transport
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R))
    {y z : Y} (hyz : y = z) :
    (StructureSheaf.toStalk R (f y) ≫ f.stalkMap y) ≫
        eqToHom (congrArg Y.presheaf.stalk hyz) =
      StructureSheaf.toStalk R (f z) ≫ f.stalkMap z := by
  subst z
  simp

end Deformation.Examples

end
