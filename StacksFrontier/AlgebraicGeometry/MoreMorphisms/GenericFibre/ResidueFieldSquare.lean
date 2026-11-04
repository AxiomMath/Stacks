module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.CommonOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec

/-!
# The residue field square over an affine base, checked on global sections

Part of Step D of the proof of Stacks Tag 0559. Stacks Tag 0552 compares two integral schemes
over a base through their residue fields at the generic points, and the datum it asks for is a
commuting square of residue field maps over the base. When the base is the spectrum of a domain
`R` and the common image of the two generic points is the generic point of `Spec R`, that square
need only be checked on global sections: the residue field of `Spec R` at the generic point is a
field of fractions of `R`
(`AlgebraicGeometry.isFractionRing_specResidueField`), so two ring homomorphisms out of it that
agree on `R` are equal.

## Main results

* `AlgebraicGeometry.residueFieldMap_comp_eq_of_appTop`: the compatibility hypothesis of
  `AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso` follows from the corresponding
  equality of the composites `Γ(Spec R, ⊤) ⟶ κ(y)`.
* `AlgebraicGeometry.exists_nonempty_open_iso_of_residueFieldIso_of_appTop`: Tag 0552 in the
  resulting form, with the square replaced by its global-sections shadow.

## Implementation notes

The hypothesis is stated with `Scheme.Hom.appTop` and `Scheme.Γevaluation` rather than with the
algebra map of `R`, so that no algebra structure has to be chosen on the two residue fields of
the sources: `Scheme.Γevaluation_naturality` is the only input, and the inverse of
`Scheme.ΓSpecIso` is inserted inside the proof, where the localization lives.

The transport `h ▸ _` of the source statement is turned into an `eqToHom` by
`AlgebraicGeometry.cast_residueField_hom`, and moved past the global evaluation map by
`Γevaluation_eqToHom`; both are proved by `cases` on the equality of points, which is why they
are stated for bound points rather than for the generic points directly.

No Stacks tag is attached: this is a reformulation of one hypothesis of Tag 0552, not a
statement of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step D of the first
  proof
* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global evaluation maps at equal points agree through the transport isomorphism. -/
private theorem Γevaluation_eqToHom {Z : Scheme.{u}} {a b : Z} (hab : a = b) :
    Z.Γevaluation a ≫ eqToHom (congrArg (fun z => Z.residueField z) hab) =
      Z.Γevaluation b := by
  cases hab
  simp

/-- Two morphisms out of a localization of `R` agree as soon as they agree on `R`. -/
private theorem hom_ext_of_isLocalization {R S T : CommRingCat.{u}} (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] {u v : S ⟶ T}
    (huv : CommRingCat.ofHom (algebraMap R S) ≫ u =
      CommRingCat.ofHom (algebraMap R S) ≫ v) :
    u = v :=
  CommRingCat.hom_ext (IsLocalization.ringHom_ext M
    (by simpa using congrArg CommRingCat.Hom.hom huv))

/-- **The compatibility square of Stacks Tag 0552, over an affine base, checked on global
sections.** Let `sX : X ⟶ Spec R` and `sY : Y ⟶ Spec R` with `R` a domain, let `x` and `y` be
points with the same image, that image being the generic point of `Spec R`, and let `g` be a
morphism of the residue fields at `x` and `y`. If the two composites out of the global sections
of `Spec R` agree, then `g` commutes with the residue field maps of `sX` and `sY`. -/
theorem residueFieldMap_comp_eq_of_appTop {R : CommRingCat.{u}} [IsDomain R] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec R) (sY : Y ⟶ Spec R) {x : X} {y : Y}
    (h : sX x = sY y) (hy : sY y = genericPoint (Spec R))
    (g : X.residueField x ⟶ Y.residueField y)
    (hglobal : sX.appTop ≫ X.Γevaluation x ≫ g = sY.appTop ≫ Y.Γevaluation y) :
    h ▸ (sX.residueFieldMap x ≫ g) = sY.residueFieldMap y := by
  rw [cast_residueField_hom h]
  let _ := specResidueFieldAlgebra R (sY y)
  have _ : IsLocalization (nonZeroDivisors R) ((Spec R).residueField (sY y)) :=
    isFractionRing_specResidueField R (sY y) hy
  have hR : (Spec R).Γevaluation (sY y) ≫ sY.residueFieldMap y =
      sY.appTop ≫ Y.Γevaluation y := Scheme.Γevaluation_naturality sY y
  have hL : (Spec R).Γevaluation (sY y) ≫
      (eqToHom (congrArg (fun z => (Spec R).residueField z) h.symm) ≫
        sX.residueFieldMap x ≫ g) = sX.appTop ≫ X.Γevaluation x ≫ g := by
    rw [← Category.assoc, Γevaluation_eqToHom h.symm, ← Category.assoc,
      Scheme.Γevaluation_naturality, Category.assoc]
  have key := hL.trans (hglobal.trans hR.symm)
  refine hom_ext_of_isLocalization (nonZeroDivisors R) ?_
  have halg : CommRingCat.ofHom (algebraMap R ((Spec R).residueField (sY y))) =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation (sY y) := rfl
  rw [halg]
  simp only [Category.assoc]
  rw [key]

/-- **Stacks Project, Tag 0552** over an affine base, with the compatibility of the residue
field isomorphism checked on global sections: two integral schemes locally of finite type over
the spectrum of a domain, whose generic points both lie over the generic point of the base and
whose residue fields there are isomorphic compatibly with the global sections, have isomorphic
nonempty open subschemes over the base. -/
theorem exists_nonempty_open_iso_of_residueFieldIso_of_appTop {R : CommRingCat.{u}} [IsDomain R]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec R) (sY : Y ⟶ Spec R) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY]
    (hX : sX (genericPoint X) = genericPoint (Spec R))
    (hY : sY (genericPoint Y) = genericPoint (Spec R))
    (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y))
    (hglobal : sX.appTop ≫ X.Γevaluation (genericPoint X) ≫ e.hom =
      sY.appTop ≫ Y.Γevaluation (genericPoint Y)) :
    ∃ (U : X.Opens) (V : Y.Opens), (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
      ∃ e' : U.toScheme ≅ V.toScheme, e'.hom ≫ V.ι ≫ sY = U.ι ≫ sX :=
  exists_nonempty_open_iso_of_residueFieldIso sX sY (hX.trans hY.symm) e
    (residueFieldMap_comp_eq_of_appTop sX sY (hX.trans hY.symm) hY e.hom hglobal)

end AlgebraicGeometry

end
