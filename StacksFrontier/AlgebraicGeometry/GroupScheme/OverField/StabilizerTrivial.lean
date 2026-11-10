module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The right stabiliser of all functions on an affine open is trivial

Let `G` be a group scheme over a field `k` which is geometrically irreducible, `T` a `k`-scheme
and `h : T ⟶ G` a `T`-point.  Right translation by `h` is the morphism
`G ×_k T ⟶ G`, `(x, t) ↦ x · h(t)`.  For an open `U` of `G`, `h` *right-stabilises* a function
`f` on `U` if on the locus of `G ×_k T` where both `x` and `x · h(t)` lie in `U` the pullbacks of
`f` along `(x, t) ↦ x` and along `(x, t) ↦ x · h(t)` agree.  This is the stabiliser of rational
functions of Perrin's thesis (I §2, IV §1).  The file proves Perrin IV 1.3: **if `h`
right-stabilises every function on one nonempty affine open, then `h = 1`.**

## Main definitions

* `AlgebraicGeometry.rightTranslate h`: the right translation `G ×_k T ⟶ G` by `h`, and
  `AlgebraicGeometry.rightShear h` the shearing automorphism `(x, t) ↦ (x · h(t), t)`.
* `AlgebraicGeometry.rightStabilizerLocus h U`: the open locus where `x` and `x · h(t)` lie in
  `U`.
* `AlgebraicGeometry.RightStabilises h U f`: `h` right-stabilises the function `f` on `U`.

## Main results

* `AlgebraicGeometry.surjective_rightStabilizerLocus`: for `U` nonempty the stabiliser locus maps
  onto `T` (the fibres of `G ×_k T ⟶ T` are irreducible and meet both opens).
* `AlgebraicGeometry.eq_one_of_forall_rightStabilises` and
  `AlgebraicGeometry.forall_rightStabilises_iff_eq_one`: **Perrin IV 1.3**.

## Implementation notes

The argument is Perrin's: on the stabiliser locus `W` the two maps to the affine scheme `U`
induce the same map on functions, hence agree (`AlgebraicGeometry.ext_of_isAffine`); as
`W`-points of `G` this reads `x = x · h(t)`, so `h(t) = 1` on `W` in the group of `W`-points;
and `W ⟶ T` is flat and surjective, hence an epimorphism
(`AlgebraicGeometry.Flat.epi_of_flat_of_surjective`).  No finiteness hypothesis on `G` or `T`
is needed; geometric irreducibility is used only for the surjectivity, and for a connected group
scheme over an algebraically closed field it is Stacks 047M
(`AlgebraicGeometry.geometricallyIrreducible_irreducibleComponent_of_identity`).

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, IV 1.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {G T : Over (Spec (.of k))} [GrpObj G]

/-- The right translation `G ×_k T ⟶ G`, `(x, t) ↦ x · h(t)`, by a `T`-point `h` of `G`. -/
noncomputable def rightTranslate (h : T ⟶ G) : G ⊗ T ⟶ G :=
  fst G T * (snd G T ≫ h)

/-- The shearing automorphism `(x, t) ↦ (x · h(t), t)` of `G ×_k T`. -/
noncomputable def rightShear (h : T ⟶ G) : G ⊗ T ≅ G ⊗ T where
  hom := lift (rightTranslate h) (snd G T)
  inv := lift (fst G T * (snd G T ≫ h)⁻¹) (snd G T)
  hom_inv_id := by
    apply hom_ext <;> simp [rightTranslate, MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  inv_hom_id := by
    apply hom_ext <;> simp [rightTranslate, MonObj.comp_mul, mul_assoc]

/-- The open locus of `G ×_k T` where both `x` and `x · h(t)` lie in `U`. -/
noncomputable def rightStabilizerLocus (h : T ⟶ G) (U : G.left.Opens) : (G ⊗ T).left.Opens :=
  (fst G T).left ⁻¹ᵁ U ⊓ (rightTranslate h).left ⁻¹ᵁ U

/-- The stabiliser locus lies in the preimage of `U` under `(x, t) ↦ x`. -/
theorem rightStabilizerLocus_le_fst (h : T ⟶ G) (U : G.left.Opens) :
    rightStabilizerLocus h U ≤ (fst G T).left ⁻¹ᵁ U :=
  inf_le_left

/-- The stabiliser locus lies in the preimage of `U` under `(x, t) ↦ x · h(t)`. -/
theorem rightStabilizerLocus_le_rightTranslate (h : T ⟶ G) (U : G.left.Opens) :
    rightStabilizerLocus h U ≤ (rightTranslate h).left ⁻¹ᵁ U :=
  inf_le_right

/-- **`h` right-stabilises the function `f` on `U`**: on the locus where `x` and `x · h(t)` lie in
`U`, the pullbacks of `f` along `(x, t) ↦ x` and `(x, t) ↦ x · h(t)` agree. -/
def RightStabilises (h : T ⟶ G) (U : G.left.Opens) (f : Γ(G.left, U)) : Prop :=
  (fst G T).left.appLE U (rightStabilizerLocus h U) (rightStabilizerLocus_le_fst h U) f =
    (rightTranslate h).left.appLE U (rightStabilizerLocus h U)
      (rightStabilizerLocus_le_rightTranslate h U) f

/-- The first coordinate of the shear `(x, t) ↦ (x · h(t), t)` is the right translation by `h`. -/
theorem rightShear_hom_fst (h : T ⟶ G) : (rightShear h).hom ≫ fst G T = rightTranslate h :=
  lift_fst _ _

/-- The inverse of the shear preserves the second coordinate `t`. -/
theorem rightShear_inv_snd (h : T ⟶ G) : (rightShear h).inv ≫ snd G T = snd G T :=
  lift_snd _ _

/-- Over a geometrically irreducible group scheme, the stabiliser locus of a nonempty open maps
onto `T` under the projection `G ×_k T ⟶ T`. -/
theorem surjective_rightStabilizerLocus [GeometricallyIrreducible G.hom] (h : T ⟶ G)
    {U : G.left.Opens} (hne : (U : Set G.left).Nonempty) :
    Surjective ((rightStabilizerLocus h U).ι ≫ (snd G T).left) := by
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨u, hu⟩ := hne
  have hopen : IsOpenMap (pullback.snd G.hom T.hom).base :=
    (pullback.snd G.hom T.hom).isOpenMap
  have hirr := Scheme.Hom.isIrreducible_preimage (pullback.snd G.hom T.hom) hopen
    (isIrreducible_singleton (x := t))
  obtain ⟨a, ha₁, ha₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := T.hom)
    u t (Subsingleton.elim _ _)
  have hfa : (fst G T).left a = u := ha₁
  have hsa : (snd G T).left a = t := ha₂
  let b := (rightShear h).inv.left a
  have hb : (rightShear h).hom.left b = a := by
    change ((rightShear h).inv ≫ (rightShear h).hom).left a = a
    rw [Iso.inv_hom_id]
    rfl
  have hρb : (rightTranslate h).left b = u := by
    rw [← rightShear_hom_fst, Over.comp_left, Scheme.Hom.comp_apply, hb, hfa]
  have hsb : (snd G T).left b = t := by
    change ((rightShear h).inv ≫ snd G T).left a = t
    rw [rightShear_inv_snd, hsa]
  obtain ⟨w, hwt, hwA, hwB⟩ := hirr.2 _ _ ((fst G T).left ⁻¹ᵁ U).isOpen
    ((rightTranslate h).left ⁻¹ᵁ U).isOpen ⟨a, hsa, show (fst G T).left a ∈ U from hfa ▸ hu⟩
    ⟨b, hsb, show (rightTranslate h).left b ∈ U from hρb ▸ hu⟩
  exact ⟨⟨w, hwA, hwB⟩, hwt⟩

/-- On the stabiliser locus, a right-stabilised affine open sees `(x, t) ↦ x` and
`(x, t) ↦ x · h(t)` as the same morphism. -/
theorem rightStabilizerLocus_ι_fst_eq [GeometricallyIrreducible G.hom] (h : T ⟶ G)
    {U : G.left.Opens} (hU : IsAffineOpen U) (hst : ∀ f, RightStabilises h U f) :
    (rightStabilizerLocus h U).ι ≫ (fst G T).left =
      (rightStabilizerLocus h U).ι ≫ (rightTranslate h).left := by
  have : IsAffine U := hU
  have hres : (fst G T).left.resLE U (rightStabilizerLocus h U) (rightStabilizerLocus_le_fst h U) =
      (rightTranslate h).left.resLE U (rightStabilizerLocus h U)
        (rightStabilizerLocus_le_rightTranslate h U) := by
    have happ : (fst G T).left.appLE U (rightStabilizerLocus h U)
          (rightStabilizerLocus_le_fst h U) =
        (rightTranslate h).left.appLE U (rightStabilizerLocus h U)
      (rightStabilizerLocus_le_rightTranslate h U) :=
      CommRingCat.hom_ext (RingHom.ext hst)
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Scheme.Hom.resLE_app_top, happ]
  exact (Scheme.Hom.resLE_comp_ι _ (rightStabilizerLocus_le_fst h U)).symm.trans
    ((congrArg (· ≫ U.ι) hres).trans
      (Scheme.Hom.resLE_comp_ι _ (rightStabilizerLocus_le_rightTranslate h U)))

/-- **Perrin, thesis IV 1.3: an element stabilising all functions on an affine open is the
identity.**  Let `G` be a geometrically irreducible group scheme over a field `k` and `h` a
`T`-point of `G`.  If `h` right-stabilises every function on one nonempty affine open `U` of `G`
(`AlgebraicGeometry.RightStabilises`), then `h = 1`. -/
theorem eq_one_of_forall_rightStabilises [GeometricallyIrreducible G.hom] (h : T ⟶ G)
    {U : G.left.Opens} (hU : IsAffineOpen U) (hne : (U : Set G.left).Nonempty)
    (hst : ∀ f, RightStabilises h U f) : h = 1 := by
  let W := rightStabilizerLocus h U
  let W' : Over (Spec (.of k)) := Over.mk (W.ι ≫ (G ⊗ T).hom)
  let w : W' ⟶ G ⊗ T := Over.homMk W.ι rfl
  have hw : w ≫ fst G T = w ≫ rightTranslate h :=
    Over.OverMorphism.ext (rightStabilizerLocus_ι_fst_eq h hU hst)
  have hone : w ≫ snd G T ≫ h = 1 := by
    have h2 : w ≫ rightTranslate h = (w ≫ fst G T) * (w ≫ snd G T ≫ h) := by
      simp [rightTranslate, MonObj.comp_mul]
    exact mul_eq_left.mp (hw.trans h2).symm
  have : Surjective (W.ι ≫ (snd G T).left) := surjective_rightStabilizerLocus h hne
  have : Flat (snd G T).left := by
    change Flat (pullback.snd G.hom T.hom)
    infer_instance
  have : Epi ((Over.forget _).map (w ≫ snd G T)) :=
    Flat.epi_of_flat_of_surjective (W.ι ≫ (snd G T).left)
  have : Epi (w ≫ snd G T) := (Over.forget _).epi_of_epi_map this
  refine (cancel_epi (w ≫ snd G T)).mp ?_
  rw [Category.assoc, hone, MonObj.comp_one]

/-- Right translation by the identity `T`-point is the projection `(x, t) ↦ x`. -/
theorem rightTranslate_one : rightTranslate (1 : T ⟶ G) = fst G T := by
  simp [rightTranslate, MonObj.comp_one]

/-- The identity right-stabilises every function. -/
theorem rightStabilises_one (U : G.left.Opens) (f : Γ(G.left, U)) :
    RightStabilises (1 : T ⟶ G) U f := by
  unfold RightStabilises
  generalize rightStabilizerLocus_le_rightTranslate (1 : T ⟶ G) U = hle
  revert hle
  rw [rightTranslate_one]
  intro hle
  rfl

/-- **The right stabiliser of all functions on a nonempty affine open is trivial**: `h`
right-stabilises every function on `U` if and only if `h = 1`. -/
theorem forall_rightStabilises_iff_eq_one [GeometricallyIrreducible G.hom] (h : T ⟶ G)
    {U : G.left.Opens} (hU : IsAffineOpen U) (hne : (U : Set G.left).Nonempty) :
    (∀ f, RightStabilises h U f) ↔ h = 1 :=
  ⟨eq_one_of_forall_rightStabilises h hU hne, fun e f ↦ e ▸ rightStabilises_one U f⟩

end AlgebraicGeometry

end
