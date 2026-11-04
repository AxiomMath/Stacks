module

public import Mathlib.FieldTheory.SeparableDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Geometric
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDown
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The geometric genus of a scheme with integral base change

Let `k` be a field with algebraic closure `k̄` and let `X` be a proper scheme over `k`.  The
geometric genus `g_geom(X/k)` is by definition a sum over the one-dimensional irreducible
components of the base change `X_{k̄}`.  When `X_{k̄}` is itself integral of dimension one that
sum has a single term, and the geometric genus is simply the genus of the normalization of
`X_{k̄}`.  Combining this with the fact that the genus does not increase along a finite morphism
and with the invariance of the genus under extension of the ground field gives the inequality
`g_geom(X/k) ≤ g(X)` in that case.

## Main results

* `AlgebraicGeometry.genus_normalizationOverField_eq_of_isIso`: an isomorphism of proper schemes
  over a field identifies the genera of their normalizations.
* `AlgebraicGeometry.geometricGenus_eq_genus_normalizationOverField`: if the base change of a
  proper scheme over `k` to an algebraic closure of `k` is irreducible, reduced and of dimension
  one, then its geometric genus is the genus of the normalization of that base change.
* `AlgebraicGeometry.geometricGenus_le_genus`: in the same situation the geometric genus is at
  most the genus.
* `AlgebraicGeometry.genus_toSpecΓ_eq_genus`: a proper integral scheme over a field whose global
  regular functions are constant has the same genus over its field of global functions as over
  the base field.
* `AlgebraicGeometry.finSepDegree_globalSections_eq_one`: in that situation the field of global
  functions has separable degree one over the base field.
* `AlgebraicGeometry.geometricGenus_le_finSepDegree_mul_genus_toSpecΓ`: the inequality of
  [Stacks, Tag 0CE5] for a proper integral scheme with constant global functions and integral
  one-dimensional base change.

## References

* [Stacks Project, Tag 0CE0](https://stacks.math.columbia.edu/tag/0CE0), Section 53.21 (Genus
  versus geometric genus)
* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Normalization and isomorphisms over a field -/

/-- An isomorphism of proper schemes over a field identifies their normalizations, so the genera
of the normalizations agree. -/
public theorem genus_normalizationOverField_eq_of_isIso {k : Type u} [Field k]
    {A B : Scheme.{u}} (a : A ⟶ Spec (.of k)) (b : B ⟶ Spec (.of k))
    [IsProper a] [IsProper b] (f : A ⟶ B) [IsIso f] (hf : f ≫ b = a) :
    genus (normalizationOverField k a ≫ a) = genus (normalizationOverField k b ≫ b) := by
  have hBfin : ∀ U : B.Opens, IsCompact (U : Set B) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyOfFiniteType k b
  have hAfin := finite_irreducibleComponents_of_smooth f hBfin
  have hsq := isPullback_normalizationSchemeMap_of_etale f hBfin
  have hcomm : normalizationSchemeMap f hAfin hBfin ≫ (B.normalization hBfin ≫ b) =
      A.normalization hAfin ≫ a := by
    rw [← Category.assoc, hsq.w, Category.assoc, hf]
  have hiso : IsIso (normalizationSchemeMap f hAfin hBfin) := by
    refine ⟨hsq.lift (𝟙 _) (B.normalization hBfin ≫ inv f) (by simp), ?_, hsq.lift_fst _ _ _⟩
    refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hsq.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hsq.lift_snd, Category.id_comp, ← Category.assoc, hsq.w,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hbproper : IsProper (B.normalization hBfin ≫ b) :=
    isProper_normalizationOverField_comp k b
  have hpull : IsPullback (normalizationSchemeMap f hAfin hBfin)
      (A.normalization hAfin ≫ a) (B.normalization hBfin ≫ b)
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    have hs : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by simp
    rw [hs]
    exact IsPullback.of_horiz_isIso ⟨by simpa using hcomm⟩
  exact genus_baseChange k k _ _ _ hpull

/-! ### The geometric genus of a scheme with integral base change -/

/-- Let `k` be a field and let `X` be a proper scheme over `k` whose base change `X_{k̄}` to an
algebraic closure of `k` is irreducible, reduced and of dimension one.  Then the geometric genus
of `X` over `k` is the genus of the normalization of `X_{k̄}` over `k̄`. -/
public theorem geometricGenus_eq_genus_normalizationOverField
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hirr : IrreducibleSpace (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hred : IsReduced (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) = 1) :
    geometricGenus k g =
      genus (normalizationOverField (AlgebraicClosure k)
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ≫
        pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) := by
  classical
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsNoetherian (pullback (C := Scheme.{u}) g a) := {}
  let : Finite (irreducibleComponents (pullback (C := Scheme.{u}) g a)) :=
    (finite_irreducibleComponents_of_isNoetherian
      (X := pullback (C := Scheme.{u}) g a)).to_subtype
  let : Fintype (irreducibleComponents (pullback (C := Scheme.{u}) g a)) := Fintype.ofFinite _
  have hZ0 : (Set.univ : Set (pullback (C := Scheme.{u}) g a)) ∈
      irreducibleComponents (pullback (C := Scheme.{u}) g a) := by
    rw [irreducibleComponents_eq_singleton]; rfl
  have key : ∀ W : irreducibleComponents (pullback (C := Scheme.{u}) g a),
      (W : Set (pullback (C := Scheme.{u}) g a)) = Set.univ := fun W ↦
    Set.eq_of_mem_singleton ((Set.ext_iff.mp irreducibleComponents_eq_singleton _).mp W.2)
  have : Subsingleton (irreducibleComponents (pullback (C := Scheme.{u}) g a)) :=
    ⟨fun W W' ↦ Subtype.ext ((key W).trans (key W').symm)⟩
  set Z0 : irreducibleComponents (pullback (C := Scheme.{u}) g a) := ⟨Set.univ, hZ0⟩
  have hbot : irreducibleComponentIdeal Z0 = ⊥ := by
    have htop : (⟨Z0.1, isClosed_of_mem_irreducibleComponents Z0.1 Z0.2⟩ : Closeds
        (pullback (C := Scheme.{u}) g a)) = ⊤ := rfl
    rw [irreducibleComponentIdeal, htop, Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.nilradical_eq_bot]
  have hiso : IsIso (irreducibleComponentIdeal Z0).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 hbot
  have hdim' : topologicalKrullDim (irreducibleComponentIdeal Z0).subscheme = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (irreducibleComponentIdeal Z0).subschemeι)).isHomeomorph]
    exact hdim
  show ∑ Z : irreducibleComponents (pullback (C := Scheme.{u}) g a),
      (if topologicalKrullDim (irreducibleComponentIdeal Z).subscheme = 1 then
        genus (normalizationOverField (AlgebraicClosure k)
            ((irreducibleComponentIdeal Z).subschemeι ≫ pullback.snd g a) ≫
          ((irreducibleComponentIdeal Z).subschemeι ≫ pullback.snd g a))
      else 0) = _
  rw [Fintype.sum_subsingleton _ Z0]
  split_ifs
  exact genus_normalizationOverField_eq_of_isIso _ _ (irreducibleComponentIdeal Z0).subschemeι rfl

/-- Let `k` be a field and let `X` be a proper scheme over `k` whose base change `X_{k̄}` to an
algebraic closure of `k` is irreducible, reduced and of dimension one.  Then the geometric genus
of `X` over `k` is at most the genus of `X`.  The three cohomological hypotheses are those of
[Stacks, Tag 0CE3] at the normalization morphism of `X_{k̄}`. -/
public theorem geometricGenus_le_genus
    (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hirr : IrreducibleSpace (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hred : IsReduced (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) = 1)
    (hcoker : IsZero (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k)
        (pullback.snd g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))))) 1))
    (hker : IsZero (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (kernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k)
        (pullback.snd g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))))) 2))
    (hfin : FiniteDimensional (AlgebraicClosure k) (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (structureSheafModule (pullback (C := Scheme.{u}) g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) 1)) :
    geometricGenus k g ≤ genus g := by
  classical
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hfinite := isFinite_normalizationOverField (AlgebraicClosure k) (pullback.snd g a)
  have hbc : genus (pullback.snd g a) = genus g :=
    genus_baseChange k (AlgebraicClosure k) (pullback.fst g a) (pullback.snd g a) g
      (IsPullback.of_hasPullback _ _)
  rw [geometricGenus_eq_genus_normalizationOverField k g hirr hred hdim, ← hbc]
  exact genus_le_of_isAffineHom_of_isZero (AlgebraicClosure k) (pullback.snd g a)
    (normalizationOverField (AlgebraicClosure k) (pullback.snd g a)) hcoker hker hfin

/-! ### The geometric genus and the separable degree of the global functions -/

/-- If the canonical homomorphism from a field `k` to the global regular functions on a proper
integral scheme `Z` over `k` is an isomorphism, then the genus of `Z` over its field of global
functions is its genus over `k`. -/
public theorem genus_toSpecΓ_eq_genus
    (k : Type u) [Field k] {Z : Scheme.{u}} [IsIntegral Z]
    (f : Z ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    letI : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
    genus Z.toSpecΓ = genus f := by
  let A := Γ(Z, ⊤)
  let : Field A := (isField_of_universallyClosed k f).toField
  let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let : Algebra k A := α.hom.toAlgebra
  let b : Spec (.of A) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : IsIso b := by
    show IsIso (Spec.map α)
    infer_instance
  have hfb : Z.toSpecΓ ≫ b = f := by
    show Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hsq : IsPullback (𝟙 Z) Z.toSpecΓ f b :=
    IsPullback.of_horiz_isIso ⟨by simpa using hfb.symm⟩
  exact genus_baseChange k A (𝟙 Z) Z.toSpecΓ f hsq

/-- If the canonical homomorphism from a field `k` to the global regular functions on a proper
integral scheme `Z` over `k` is an isomorphism, then that field of global functions has separable
degree one over `k`. -/
public theorem finSepDegree_globalSections_eq_one
    (k : Type u) [Field k] {Z : Scheme.{u}} [IsIntegral Z]
    (f : Z ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    letI : Field Γ(Z, ⊤) := (isField_of_universallyClosed k f).toField
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Field.finSepDegree k Γ(Z, ⊤) = 1 := by
  let A := Γ(Z, ⊤)
  let : Field A := (isField_of_universallyClosed k f).toField
  let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let : Algebra k A := α.hom.toAlgebra
  have hbij : Function.Bijective (algebraMap k A) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      ConcreteCategory.bijective_of_isIso (C := CommRingCat) α
  exact (Field.finSepDegree_eq_of_equiv k k A
    (AlgEquiv.ofBijective (Algebra.ofId k A) hbij)).symm.trans (Field.finSepDegree_self k)

/-- Let `k` be a field and let `X` be a proper integral scheme over `k` whose global regular
functions are exactly `k` and whose base change to an algebraic closure of `k` is irreducible,
reduced and of dimension one.  Writing `κ = Γ(X, ⊤)`, the geometric genus of `X` over `k` is at
most `[κ : k]_s · dim_κ H¹(X, 𝒪_X)`. -/
@[stacks 0CE5 "κ = k, geometrically integral of dim 1, 0CE3's vanishings and H¹ finite"]
public theorem geometricGenus_le_finSepDegree_mul_genus_toSpecΓ
    (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Spec (.of k)) [IsProper g]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop)]
    (hirr : IrreducibleSpace (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hred : IsReduced (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) g
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) = 1)
    (hcoker : IsZero (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (cokernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k)
        (pullback.snd g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))))) 1))
    (hker : IsZero (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (kernel (structureSheafToPushforward (normalizationOverField (AlgebraicClosure k)
        (pullback.snd g
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))))) 2))
    (hfin : FiniteDimensional (AlgebraicClosure k) (cohomologyOverField (AlgebraicClosure k)
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
      (structureSheafModule (pullback (C := Scheme.{u}) g
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) 1)) :
    letI : Field Γ(X, ⊤) := (isField_of_universallyClosed k g).toField
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    geometricGenus k g ≤ Field.finSepDegree k Γ(X, ⊤) * genus X.toSpecΓ := by
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k g).toField
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have h1 : Field.finSepDegree k Γ(X, ⊤) = 1 := finSepDegree_globalSections_eq_one k g
  have h2 : genus X.toSpecΓ = genus g := genus_toSpecΓ_eq_genus k g
  show geometricGenus k g ≤ Field.finSepDegree k Γ(X, ⊤) * genus X.toSpecΓ
  rw [h1, one_mul, h2]
  exact geometricGenus_le_genus k g hirr hred hdim hcoker hker hfin

end AlgebraicGeometry

end
