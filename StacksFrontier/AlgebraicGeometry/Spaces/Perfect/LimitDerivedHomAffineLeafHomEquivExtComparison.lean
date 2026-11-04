module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineObjects

/-!
# The chosen derived extension of scalars at a K-flat complex is termwise extension of scalars

`AlgebraicGeometry.Space.representedAffineDerivedExtension B S hS g` is the chosen total derived
extension of scalars `- ⊗^𝐋_R R'` along the map of rings of global functions of a morphism
`g : U' ⟶ U` of affine representables.  `Stacks.LimitHomDescent.Affine.ext` is *termwise*
extension of scalars on cochain complexes.  The two are compared by the structure field
`comparison`, whose codomain is — on the nose, though no lemma recorded it — termwise extension
of scalars followed by the localization functor of the derived category:

`(representedAffineDerivedExtension B S hS g).functor.obj (Q.obj C) ⟶ Q.obj ((ext φ).obj C)`.

**The comparison is not invertible for arbitrary `C`**: derived tensor product is not termwise
tensor product, and the chosen functor is the *left derived* functor of the termwise one.  It is
invertible exactly at the complexes that compute it, and the structure asserts this for the
K-flat ones (`comparison_isIso_of_kFlat`, which is how Section 06Y5 defines the functor).  This
is no loss for the affine leaf of Stacks 09RI: every object of `D(R)` has a K-flat representative
(`Stacks.LimitHomDescent.Affine.RingSystem.exists_kFlat_iso`), so the K-flat form of the
comparison already identifies the derived extension of scalars of *any* object of `D(R)` with the
localization of a termwise extension of scalars — which is
`AlgebraicGeometry.Space.exists_kFlat_iso_representedAffineDerivedExtension`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineDerivedExtensionObjIsoQExt`: the comparison at a
  K-flat complex, as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedExtensionComparisonApp`: the comparison of
  the chosen model goes from the derived extension of scalars of the localization to the
  localization of the termwise extension of scalars.  This records the identification of the
  codomain.
* `AlgebraicGeometry.Space.exists_kFlat_iso_representedAffineDerivedExtension`: for every object
  of `D(R)` there is a K-flat complex representing it whose termwise extension of scalars
  localizes to the derived extension of scalars of that object.

## References

* [Stacks Project, Section 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

/- No affineness is needed anywhere in this file: the chosen derived extension of scalars along
`g` is the one along the map of rings of global functions, and the comparison with termwise
extension of scalars is a statement about that ring map alone. -/
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} (g : U' ⟶ U)

/-- **The comparison of the chosen derived extension of scalars goes to the localization of the
termwise extension of scalars.**  The codomain of the structure field `comparison` of
`AlgebraicGeometry.Space.representedAffineDerivedExtension` is
`Stacks.LimitHomDescent.Affine.ext` of the map of rings of global functions, followed by
`DerivedCategory.Q`.  This records that identification; it holds on the nose. -/
def representedAffineDerivedExtensionComparisonApp
    (C : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedExtension B S hS g).functor.obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj ((Stacks.LimitHomDescent.Affine.ext
        (representedAffineCommRingCatHom B S hS g)).obj C) :=
  (representedAffineDerivedExtension B S hS g).comparison.app C

/-- **The comparison of the chosen derived extension of scalars is invertible at a K-flat
complex.**  This is the structure field `comparison_isIso_of_kFlat` of
`AlgebraicGeometry.Space.representedAffineDerivedExtension`: K-flat complexes compute derived
extension of scalars, which is how Section 06Y5 defines the functor. -/
theorem isIso_representedAffineDerivedExtension_comparison_app_of_kFlat
    (C : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hC : C.KFlat) :
    IsIso ((representedAffineDerivedExtension B S hS g).comparison.app C) :=
  (representedAffineDerivedExtension B S hS g).comparison_isIso_of_kFlat C hC

/-- **At a K-flat complex the chosen derived extension of scalars is the termwise extension of
scalars**: `(C ⊗^𝐋_R R') ≅ (R' ⊗_R C)` in `D(R')`, for `C` K-flat.

It is *only* at such complexes: the comparison is the unit exhibiting the chosen functor as the
total left derived functor of the termwise one, and a complex that is not K-flat need not
compute it. -/
def representedAffineDerivedExtensionObjIsoQExt
    (C : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hC : C.KFlat) :
    (representedAffineDerivedExtension B S hS g).functor.obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((Stacks.LimitHomDescent.Affine.ext
        (representedAffineCommRingCatHom B S hS g)).obj C) :=
  @asIso _ _ _ _ (representedAffineDerivedExtensionComparisonApp B S hS g C)
    (isIso_representedAffineDerivedExtension_comparison_app_of_kFlat B S hS g C hC)

/-- The isomorphism at a K-flat complex is the comparison of the chosen model. -/
@[simp]
theorem representedAffineDerivedExtensionObjIsoQExt_hom
    (C : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (hC : C.KFlat) :
    (representedAffineDerivedExtensionObjIsoQExt B S hS g C hC).hom =
      (representedAffineDerivedExtension B S hS g).comparison.app C :=
  rfl

/-- **Every object of `D(R)` has a K-flat representative whose termwise extension of scalars
computes its derived extension of scalars.**  The derived extension of scalars of an *arbitrary*
object of `D(R)` is therefore the localization of a termwise extension of scalars — which is what
the affine leaf of Stacks 09RI consumes, and why the K-flatness in
`AlgebraicGeometry.Space.representedAffineDerivedExtensionObjIsoQExt` costs nothing there. -/
theorem exists_kFlat_iso_representedAffineDerivedExtension
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    ∃ C : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ, C.KFlat ∧
      Nonempty (DerivedCategory.Q.obj C ≅ M) ∧
      Nonempty ((representedAffineDerivedExtension B S hS g).functor.obj M ≅
        DerivedCategory.Q.obj ((Stacks.LimitHomDescent.Affine.ext
          (representedAffineCommRingCatHom B S hS g)).obj C)) := by
  obtain ⟨C, hC, ⟨e⟩⟩ := Stacks.LimitHomDescent.Affine.RingSystem.exists_kFlat_iso M
  exact ⟨C, hC, ⟨e⟩, ⟨(representedAffineDerivedExtension B S hS g).functor.mapIso e.symm ≪≫
    representedAffineDerivedExtensionObjIsoQExt B S hS g C hC⟩⟩

end AlgebraicGeometry.Space

end
