module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz

/-!
# Large field extensions make a scheme Jacobson

A scheme over a field admits an affine open covering such that, after extension to any field of
cardinality exceeding the size of the scheme, every member of the base-changed covering is
Jacobson and its closed points have algebraic residue fields over the new base field.  Gluing
over the covering, the whole base change is then a Jacobson space.

## Main results

* `AlgebraicGeometry.exists_affineOpenCover_jacobson_and_isAlgebraic_residueField_withBound`
  supplies the affine covering, with `X.size` itself as the cardinal bound.
* `AlgebraicGeometry.exists_affineOpenCover_jacobson_and_isAlgebraic_residueField` is the same
  statement with the cardinal bound existentially quantified.
* `AlgebraicGeometry.jacobsonSpace_pullback_of_large_cardinality` states that sufficiently
  large field extensions make the base change of a scheme Jacobson.

## Implementation notes

An open `U` is base changed by pulling back the restricted structure morphism `U.ι ≫ f` along
`Spec K ⟶ Spec k`.  The algebra structure on the residue field of a point is the canonical one
induced by the structure morphism to `Spec K` and the standard identification of the residue
field of the unique point of `Spec K` with `K`.  The cardinal bound is the size of the scheme,
so that each ring of sections of a member of the covering is smaller than the extension field
and the uncountable Nullstellensatz applies.

In `exists_affineOpenCover_jacobson_and_isAlgebraic_residueField_withBound` that bound is
*stated* as `X.size` rather than existentially quantified.  A caller working in a big fppf site
needs to know the bound lies below the site's cutoff in order to exhibit an extension field
whose spectrum is still an object of the site, and an opaque `∃ κ` does not supply that.  The
phrase "cardinality is large enough" is expressed by the existence of a cardinal lower bound in
`exists_affineOpenCover_jacobson_and_isAlgebraic_residueField` and in
`jacobsonSpace_pullback_of_large_cardinality`, whose conclusion mentions no covering.

## References

* [Stacks Project, Tag 0479](https://stacks.math.columbia.edu/tag/0479)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry CommRingCat

namespace AlgebraicGeometry

universe u

/-- The canonical algebra structure on the residue field at a point of a spectrum is
transported along an equality of points. -/
private lemma spec_residueField_scalar_congr (R : CommRingCat) (x y : Spec R)
    [x.asIdeal.IsPrime] [y.asIdeal.IsPrime] (h : x = y) :
    CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R x).inv ≫
          (Scheme.residueFieldCongr h).hom =
      CommRingCat.ofHom (algebraMap R y.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R y).inv := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

/-- A scheme over a field has an affine open covering such that base change to any field of
cardinality exceeding the size of the scheme makes every member Jacobson, with algebraic residue
fields at all closed points.

The cardinal bound is `X.size` itself, stated rather than merely asserted to exist, so that a
caller working inside a big fppf site can compare it with the site's cutoff and thereby produce
an extension field whose spectrum still belongs to the site.  Existentially quantifying the
bound recovers `exists_affineOpenCover_jacobson_and_isAlgebraic_residueField`. -/
theorem exists_affineOpenCover_jacobson_and_isAlgebraic_residueField_withBound
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ∃ (ι : Type u) (U : ι → X.Opens),
      IsOpenCover U ∧
        ((∀ i, IsAffineOpen (U i)) ∧
          (∀ (K : Type u) [Field K] [Algebra k K], Cardinal.mk K > X.size →
            ∀ i,
              let Y := pullback (C := Scheme.{u}) ((U i).ι ≫ f)
                (Spec.map (ofHom (algebraMap k K)))
              let g : Y ⟶ Spec (.of K) := pullback.snd (C := Scheme.{u}) ((U i).ι ≫ f)
                (Spec.map (ofHom (algebraMap k K)))
              JacobsonSpace Y ∧
                (∀ x : Y,
                  IsClosed ({x} : Set _) →
                    letI : (g x).asIdeal.IsPrime := (g x).isPrime
                    letI := ((ofHom (algebraMap K (g x).asIdeal.ResidueField)) ≫
                      (Scheme.Spec.residueFieldIso (.of K) (g x)).inv ≫
                      g.residueFieldMap x).hom.toAlgebra
                    Algebra.IsAlgebraic K (Y.residueField x)))) := by
  classical
  have hSpec : ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (q : Spec S)
      [(Spec.map φ q).asIdeal.IsPrime] [q.asIdeal.IsPrime],
      ofHom (algebraMap R (Spec.map φ q).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso R (Spec.map φ q)).inv ≫ (Spec.map φ).residueFieldMap q =
        φ ≫ ofHom (algebraMap S q.asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso S q).inv := by
    intro R S φ q _ _
    calc
      _ = (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ q) (by simp) ≫
            (Spec R).residue _ ≫ (Spec.map φ).residueFieldMap q :=
        congrArg (· ≫ (Spec.map φ).residueFieldMap q)
          (Scheme.Spec.algebraMap_residueFieldIso_inv R _)
      _ = (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ q) (by simp) ≫
            (Spec.map φ).stalkMap q ≫ (Spec S).residue q := by
        rw [Scheme.residue_residueFieldMap]
      _ = (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop ≫ (Spec S).presheaf.germ ⊤ q (by simp) ≫
            (Spec S).residue q := by
        rw [Scheme.Hom.germ_stalkMap_assoc]
        simp
      _ = _ := by
        rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Spec.algebraMap_residueFieldIso_inv]
  have hcomp : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {Y : Scheme.{u}}
      (h : Y ⟶ Spec (.of S)) (g : Y ⟶ Spec (.of R))
      (_ : h ≫ Spec.map (ofHom (algebraMap R S)) = g) (x : Y) [(g x).asIdeal.IsPrime]
      [(h x).asIdeal.IsPrime],
      ofHom (algebraMap R (g x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of R) (g x)).inv ≫ g.residueFieldMap x =
        ofHom (algebraMap R (h x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of S) (h x)).inv ≫ h.residueFieldMap x := by
    intro R S _ _ _ Y h g hg x _ _
    subst hg
    have : (Spec.map (ofHom (algebraMap R S)) (h x)).asIdeal.IsPrime := PrimeSpectrum.isPrime _
    have := congrArg (· ≫ h.residueFieldMap x)
      (hSpec (ofHom (algebraMap R S)) (h x))
    rw [Scheme.residueFieldMap_comp, IsScalarTower.algebraMap_eq R S (h x).asIdeal.ResidueField,
      CommRingCat.ofHom_comp]
    simp only [Category.assoc] at this ⊢
    exact this
  have key : ∀ {K T : Type u} [Field K] [CommRing T] [Algebra K T] [IsJacobsonRing T]
      {Y : Scheme.{u}} (e : Y ≅ Spec (.of T)) (g : Y ⟶ Spec (.of K))
      (_ : e.hom ≫ Spec.map (ofHom (algebraMap K T)) = g)
      (_ : ∀ (m : Ideal T) [m.IsMaximal], Algebra.IsAlgebraic K (T ⧸ m)),
      JacobsonSpace Y ∧
        ∀ x : Y, IsClosed ({x} : Set _) →
          have : (g x).asIdeal.IsPrime := (g x).isPrime
          let := ((ofHom (algebraMap K (g x).asIdeal.ResidueField)) ≫
            (Scheme.Spec.residueFieldIso (.of K) (g x)).inv ≫ g.residueFieldMap x).hom.toAlgebra
          Algebra.IsAlgebraic K (Y.residueField x) := by
    intro K T _ _ _ _ Y e g hg halg
    have : JacobsonSpace (Spec (.of T)) := by
      change JacobsonSpace (PrimeSpectrum T)
      exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp ‹_›
    refine ⟨.of_isClosedEmbedding e.hom.homeomorph.isClosedEmbedding, fun x hx => ?_⟩
    let q := e.hom x
    have : (g x).asIdeal.IsPrime := (g x).isPrime
    have : q.asIdeal.IsPrime := q.isPrime
    have hq : IsClosed ({q} : Set (Spec (.of T))) := by
      simpa [q] using
        e.hom.homeomorph.isClosedEmbedding.isClosed_iff_image_isClosed (s := {x}) |>.mp hx
    have : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq
    have := halg q.asIdeal
    have hres : Algebra.IsAlgebraic K q.asIdeal.ResidueField :=
      Algebra.isAlgebraic_iff_isIntegral.mpr <| Algebra.IsIntegral.of_surjective
        (IsScalarTower.toAlgHom K (T ⧸ q.asIdeal) q.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal).2
    let F := (Scheme.Spec.residueFieldIso (.of T) q).inv ≫ e.hom.residueFieldMap x
    let : Algebra K (Y.residueField x) :=
      ((ofHom (algebraMap K (g x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of K) (g x)).inv ≫ g.residueFieldMap x).hom).toAlgebra
    have hscalar : ofHom (algebraMap K (Y.residueField x)) =
        ofHom (algebraMap K q.asIdeal.ResidueField) ≫ F :=
      hcomp e.hom g hg x
    let : Algebra q.asIdeal.ResidueField (Y.residueField x) := F.hom.toAlgebra
    have : IsScalarTower K q.asIdeal.ResidueField (Y.residueField x) :=
      .of_algebraMap_eq' (by
        simpa [F, RingHom.algebraMap_toAlgebra] using
          congrArg (fun z : CommRingCat.of K ⟶ CommRingCat.of (Y.residueField x) => z.hom)
            hscalar)
    exact (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K q.asIdeal.ResidueField
      (Y.residueField x)) (ConcreteCategory.bijective_of_isIso F)).isAlgebraic_iff.mp hres
  refine ⟨_, _, X.affineCover.isOpenCover_opensRange,
    fun i => isAffineOpen_opensRange (X.affineCover.f i), fun K _ _ hK i => ?_⟩
  let V : X.Opens := (X.affineCover.f i).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange (X.affineCover.f i)
  let R : Type u := Γ(X, V)
  have hle : V ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let : Algebra k R := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V hle).hom.toAlgebra
  let fR : Spec (.of R) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k R))
  let fK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k K))
  have hfV : hV.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V hle) =
      V.ι ≫ f := by
    have htop : (⊤ : (Spec (.of k)).Opens).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv =
        (⊤ : (Spec (.of k)).Opens).ι := by
      rw [← Scheme.isoSpec_Spec_inv, Scheme.Opens.toSpecΓ_top, Category.assoc,
        Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
    rw [hV.isoSpec_hom, Spec.map_comp, ← Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc, htop]
    simp
  have hY : IsPullback (pullback.fst (V.ι ≫ f) fK ≫ hV.isoSpec.hom)
      (pullback.snd (V.ι ≫ f) fK) fR fK :=
    (IsPullback.of_hasPullback (V.ι ≫ f) fK).of_iso (Iso.refl _) hV.isoSpec (Iso.refl _)
      (Iso.refl _) rfl rfl hfV.symm rfl
  let e₀ := hY.isoIsPullback _ _ (IsPullback.of_hasPullback fR fK)
  let e₂ := e₀ ≪≫ pullbackSymmetry fR fK ≪≫ pullbackSpecIso k K R
  have hφ : ofHom (algebraMap K (TensorProduct k K R)) =
      ofHom Algebra.TensorProduct.includeLeftRingHom := by
    ext a
    simp
  have hg : e₂.hom ≫ Spec.map (ofHom (algebraMap K (TensorProduct k K R))) =
      pullback.snd (V.ι ≫ f) fK := by
    rw [hφ]
    simp only [e₂, e₀, fK, fR, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst,
      pullbackSymmetry_hom_comp_fst]
    exact IsPullback.isoIsPullback_hom_snd _ _ hY (IsPullback.of_hasPullback fR fK)
  have hcard : Cardinal.lift.{u} (Cardinal.mk R) < Cardinal.lift.{u} (Cardinal.mk K) := by
    simpa using (X.mk_sections_le_size ⟨V, hV⟩).trans_lt hK
  have := isJacobsonRing_tensorProduct_of_card_lt k R K hcard
  exact key e₂ _ hg fun m _ =>
    Algebra.isAlgebraic_tensorProduct_quotient_of_card_lt k R K hcard m

/-- A scheme over a field has an affine open covering with a common cardinal bound such that
base change to any larger field makes every member Jacobson, with algebraic residue fields at
all closed points. -/
theorem exists_affineOpenCover_jacobson_and_isAlgebraic_residueField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ∃ (ι : Type u) (U : ι → X.Opens) (κ : Cardinal.{u}),
      IsOpenCover U ∧
        ((∀ i, IsAffineOpen (U i)) ∧
          (∀ (K : Type u) [Field K] [Algebra k K], Cardinal.mk K > κ →
            ∀ i,
              let Y := pullback (C := Scheme.{u}) ((U i).ι ≫ f)
                (Spec.map (ofHom (algebraMap k K)))
              let g : Y ⟶ Spec (.of K) := pullback.snd (C := Scheme.{u}) ((U i).ι ≫ f)
                (Spec.map (ofHom (algebraMap k K)))
              JacobsonSpace Y ∧
                (∀ x : Y,
                  IsClosed ({x} : Set _) →
                    letI : (g x).asIdeal.IsPrime := (g x).isPrime
                    letI := ((ofHom (algebraMap K (g x).asIdeal.ResidueField)) ≫
                      (Scheme.Spec.residueFieldIso (.of K) (g x)).inv ≫
                      g.residueFieldMap x).hom.toAlgebra
                    Algebra.IsAlgebraic K (Y.residueField x)))) := by
  obtain ⟨ι, U, hU, hAffine, hJ⟩ :=
    exists_affineOpenCover_jacobson_and_isAlgebraic_residueField_withBound k X f
  exact ⟨ι, U, X.size, hU, hAffine, hJ⟩

/-- **The base change of a scheme to a field larger than the scheme is Jacobson.** Let `X` be a
scheme over a field `k` and `K/k` an extension with `#K` above the size of `X`. Then `X_K` is a
Jacobson scheme: it is covered by the base changes of the affine opens of `X`, each of which is
Jacobson. -/
theorem jacobsonSpace_pullback_of_size_lt
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K] (hK : X.size < Cardinal.mk K) :
    JacobsonSpace ↑(pullback f (Spec.map (ofHom (algebraMap k K)))) := by
  obtain ⟨ι, U, hU, _, hJ⟩ :=
    exists_affineOpenCover_jacobson_and_isAlgebraic_residueField_withBound k X f
  let 𝒱 := Scheme.Pullback.openCoverOfLeft (Scheme.openCoverOfIsOpenCover X U hU) f
    (Spec.map (ofHom (algebraMap k K)))
  rw [(𝒱.isOpenCover_opensRange).jacobsonSpace_iff]
  intro i
  have hJi : JacobsonSpace (𝒱.X i) := by
    change JacobsonSpace (pullback (C := Scheme.{u}) ((U i).ι ≫ f)
      (Spec.map (ofHom (algebraMap k K))))
    simpa [𝒱, Scheme.Pullback.openCoverOfLeft_X] using (hJ K hK i).1
  exact hJi.of_isClosedEmbedding
    (𝒱.f i).isOpenEmbedding.isEmbedding.toHomeomorph.symm.isClosedEmbedding

/-- The base change of a scheme to every sufficiently large extension of its ground field is a
Jacobson scheme. -/
@[stacks 0479 "base_change_jacobson"]
theorem jacobsonSpace_pullback_of_large_cardinality
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    ∃ κ : Cardinal.{u}, ∀ (K : Type u) [Field K] [Algebra k K],
      κ ≤ Cardinal.mk K →
        JacobsonSpace ↑(pullback f (Spec.map (ofHom (algebraMap k K)))) :=
  ⟨Order.succ X.size, fun K _ _ hK =>
    jacobsonSpace_pullback_of_size_lt k X f K ((Order.lt_succ X.size).trans_le hK)⟩

end AlgebraicGeometry

end
