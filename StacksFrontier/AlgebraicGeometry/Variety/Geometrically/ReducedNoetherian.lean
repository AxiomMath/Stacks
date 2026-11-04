module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.GermInjective
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.FieldTheory.PerfectClosure
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE

/-!
# Geometric reducedness near a point of a locally Noetherian scheme

If a locally Noetherian scheme over a field is geometrically reduced at a point, then some open
neighbourhood of that point is geometrically reduced over the field.

## Main results

* `AlgebraicGeometry.exists_open_geometricallyReduced_of_isGeometricallyReducedAt` gives the
  geometrically reduced open neighbourhood.

## Implementation notes

The open neighbourhood is represented by `U : X.Opens`, and its structure morphism over the
field is the restriction `U.ι ≫ f` of the given structure morphism.

The neighbourhood produced is an affine open on which the germ map to the local ring at the
point is injective, which exists because the scheme is locally Noetherian. Geometric reducedness
of the local ring then descends along that injection to the ring of sections, and the resulting
statement about the spectrum of those sections is transported to `U` along its canonical
isomorphism with that spectrum.

## References

* [Stacks Project, Tag 0360](https://stacks.math.columbia.edu/tag/0360)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- The structure morphism of a geometrically reduced algebra over a field is a geometrically
reduced morphism of schemes. -/
private theorem geometricallyReduced_specMap_of_isGeometricallyReduced
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (hA : Algebra.IsGeometricallyReduced k A) :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  have hbase := ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) A
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 6 5).mp hA
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have : _root_.IsReduced (K ⊗[k] A) := hbase K
  have : IsReduced (Spec (.of (A ⊗[k] K))) :=
    (AlgebraicGeometry.affine_isReduced_iff (.of (A ⊗[k] K))).2
      (isReduced_of_injective (Algebra.TensorProduct.comm k A K) (AlgEquiv.injective _))
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k A K).hom

/-- **Stacks Project, Tag 0360.** A locally Noetherian scheme that is geometrically reduced at a
point has a geometrically reduced open neighbourhood of that point. -/
@[stacks 0360, ega "IV 4.6.13" "(a) ⇒ (f)"]
public theorem exists_open_geometricallyReduced_of_isGeometricallyReducedAt
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (x : X) (hx : IsGeometricallyReducedAt f x) :
    ∃ U : X.Opens, x ∈ U ∧ GeometricallyReduced (U.ι ≫ f) := by
  obtain ⟨U, hxU, hU, hgerm⟩ :=
    exists_affineOpen_germ_injective_of_isLocallyNoetherian X x
  let A := Γ(X, U)
  let B := X.presheaf.stalk x
  have hpre : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let halg : k →+* (↑A) := by
    simpa only [Scheme.ΓSpecIso_inv, CommRingCat.ofHom_hom] using
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U hpre).hom)
  let : Algebra k (↑A) := halg.toAlgebra
  let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let baseGerm : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (f.base x) :=
    (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (f.base x) (by simp)
  have hbase : algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)) = baseGerm.hom := by
    ext d
    rfl
  let : Algebra k (↑B) := ((f.stalkMap x).hom.comp
    (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  let : Algebra (↑A) (↑B) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsScalarTower k (↑A) (↑B) := IsScalarTower.of_algebraMap_eq' (by
    ext c
    show (f.stalkMap x).hom
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)) c) =
      X.presheaf.germ U x hxU (halg c)
    calc
      _ = X.presheaf.germ (f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)) x (by simp)
          ((f.app ⊤) ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := by
        rw [hbase]
        show (f.stalkMap x).hom (baseGerm.hom c) = _
        dsimp [baseGerm]
        exact Scheme.Hom.germ_stalkMap_apply f ⊤ x (by simp)
          ((Scheme.ΓSpecIso (.of k)).inv.hom c)
      _ = X.presheaf.germ U x hxU (halg c) := by
        rw [← X.presheaf.germ_res_apply (homOfLE hpre) x hxU]
        rfl)
  have : Algebra.IsGeometricallyReduced k (↑B) :=
    (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f x).mp hx
  let s : Spec (.of (↑A)) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hs : GeometricallyReduced s := geometricallyReduced_specMap_of_isGeometricallyReduced
    (Algebra.IsGeometricallyReduced.of_injective (IsScalarTower.toAlgHom k (↑A) (↑B)) hgerm)
  have hfactor : hU.isoSpec.hom ≫ s = U.ι ≫ f := by
    have hmap : CommRingCat.ofHom (algebraMap k (↑A)) =
        (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U hpre := by
      simp [halg, RingHom.algebraMap_toAlgebra]
    calc
      hU.isoSpec.hom ≫ s = U.toSpecΓ ≫
          Spec.map (f.appLE ⊤ U hpre) ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
        rw [hU.isoSpec_hom]
        dsimp [s]
        rw [← Spec.map_comp, hmap]
      _ = (f.resLE ⊤ U hpre ≫ (⊤ : (Spec (.of k)).Opens).toSpecΓ) ≫
          Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
        exact congrArg (fun g ↦ g ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv)
          (Scheme.Opens.toSpecΓ_SpecMap_appLE f ⊤ U hpre)
      _ = U.ι ≫ f := by
        rw [Scheme.Opens.toSpecΓ_top, Category.assoc]
        simp [Scheme.Hom.resLE_comp_ι]
  refine ⟨U, hxU, ?_⟩
  rw [GeometricallyReduced.eq_geometrically, ← hfactor]
  exact MorphismProperty.cancel_left_of_respectsIso (P := geometrically IsReduced)
    hU.isoSpec.hom s |>.mpr (GeometricallyReduced.eq_geometrically ▸ hs)

end AlgebraicGeometry
