module

public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.TangentIdentity
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified

/-!
# The differential of multiplication by an integer at the identity

For a group scheme `G` over a base `S` and a point `s` of `S`, multiplication by a positive
integer `n` acts on the tangent space of `G/S` at the identity point over `s` as multiplication
by `n`. Consequently, when `n` is invertible in the residue field there, multiplication by `n` is
unramified at that identity point.

## Main results

* `AlgebraicGeometry.pullbackLift_comp_mul_eq_add`: two tangent vectors at the identity,
  paired into the fibre product and composed with the multiplication, give their sum. This is
  [Stacks, Tag 0BF5] (`AlgebraicGeometry.tangentMap_mul_at_identity`) read on dual-number arrows.
* `AlgebraicGeometry.comp_pow_id_left_eq_nsmul`: a tangent vector at the identity followed by
  multiplication by `n + 1` is `n + 1` times the tangent vector.
* `AlgebraicGeometry.injective_tangentMap_pow_id_left`: the differential of multiplication by
  `n + 1` at the identity is injective when `n + 1` is invertible in the residue field.
* `AlgebraicGeometry.unramifiedAt_pow_id_left`: multiplication by `n + 1` is then unramified at
  the identity, by [Stacks, Tag 0B2G].

## Implementation notes

Tag 0BF5 is stated through the tangent map of the multiplication and the decomposition of the
tangent space of a fibre product (Tag 0BEB), with the residue fields of the points involved
identified by canonical isomorphisms. `AlgebraicGeometry.pullbackLift_comp_mul_eq_add` removes
those identifications: the composite of the dual-number isomorphisms that appear is the identity,
because all of them are induced by the common map to the base.

Multiplication by `n` is the `n`-th power of the identity in the group `G ⟶ G`, so it is computed
on a tangent vector `θ` by induction from `[n + 1] = [n] * 𝟙`, which makes `θ ≫ [n + 1]` the lift
of the pair `(θ ≫ [n], θ)` followed by the multiplication.

## References

* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- On spectra, composing the dual-number isomorphisms induced by two composable ring
isomorphisms is the dual-number isomorphism induced by their composite. -/
lemma specMap_dualNumberCongr_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (e₁ : A ≃+* B) (e₂ : B ≃+* C) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e₂).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e₁).toRingHom) =
      Spec.map (CommRingCat.ofHom (dualNumberCongr (e₁.trans e₂)).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- Two morphisms `a b : P ⟶ X` which agree after `i : X ⟶ S` and send `z` to the same point `y`,
at which `i` induces an isomorphism of residue fields, induce the same isomorphism `κ(y) ≃ κ(z)`
once `κ(a z)` and `κ(b z)` are identified with `κ(y)`. -/
theorem residueFieldCongr_trans_residueFieldMap_eq
    {P X S : Scheme.{u}} (i : X ⟶ S) (a b : P ⟶ X)
    (z : P) (y : X) (hab : a ≫ i = b ≫ i)
    (ha : a z = y) (hb : b z = y)
    [IsIso (i.residueFieldMap y)] [IsIso (a.residueFieldMap z)] [IsIso (b.residueFieldMap z)] :
    (X.residueFieldCongr ha.symm).commRingCatIsoToRingEquiv.trans
        (asIso (a.residueFieldMap z)).commRingCatIsoToRingEquiv =
      (X.residueFieldCongr hb.symm).commRingCatIsoToRingEquiv.trans
        (asIso (b.residueFieldMap z)).commRingCatIsoToRingEquiv := by
  have key : (X.residueFieldCongr ha).inv ≫ a.residueFieldMap z =
      (X.residueFieldCongr hb).inv ≫ b.residueFieldMap z := by
    let cA := X.residueFieldCongr ha
    let cB := X.residueFieldCongr hb
    let cSA := S.residueFieldCongr (congrArg i ha)
    let cSB := S.residueFieldCongr (congrArg i hb)
    have hGA : i.residueFieldMap (a z) = cSA.hom ≫ i.residueFieldMap y ≫ cA.inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact Scheme.Hom.residueFieldMap_congr' (f := i) ha
    have hGB : i.residueFieldMap (b z) = cSB.hom ≫ i.residueFieldMap y ≫ cB.inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact Scheme.Hom.residueFieldMap_congr' (f := i) hb
    have hbasez : (a ≫ i) z = (b ≫ i) z := by
      simpa using congrArg i (ha.trans hb.symm)
    have hpath : cSA.hom = (S.residueFieldCongr hbasez).hom ≫ cSB.hom := by
      have hpath' : cSA.hom =
          (S.residueFieldCongr (hbasez.trans (congrArg i hb))).hom :=
        congrArg (fun h => (S.residueFieldCongr h).hom) (Subsingleton.elim _ _)
      have ht := (Scheme.residueFieldCongr_trans_hom S hbasez (congrArg i hb)).symm
      change (S.residueFieldCongr (hbasez.trans (congrArg i hb))).hom =
        (S.residueFieldCongr hbasez).hom ≫ cSB.hom at ht
      exact hpath'.trans ht
    have hcomp : (a ≫ i).residueFieldMap z =
        (S.residueFieldCongr hbasez).hom ≫ (b ≫ i).residueFieldMap z := by
      simpa [hbasez] using Scheme.Hom.residueFieldMap_congr hab z
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp, hGA, hGB] at hcomp
    have hcomp' : i.residueFieldMap y ≫ cA.inv ≫ a.residueFieldMap z =
        i.residueFieldMap y ≫ cB.inv ≫ b.residueFieldMap z := by
      simpa [Category.assoc, hpath] using hcomp
    exact (cancel_epi (i.residueFieldMap y)).1 hcomp'
  exact RingEquiv.ext fun x => congrArg (fun f => CommRingCat.Hom.hom f x) key

/-- Transporting a tangent arrow along an equality of points `x = y` and precomposing with the
dual-number isomorphism induced by `e : κ(y) ≃ K` is precomposing the original arrow with the
dual-number isomorphism induced by the identification `κ(x) ≃ κ(y)` followed by `e`. -/
theorem specMap_comp_dottedTangentArrow_cast {X S : Scheme.{u}} (f : X ⟶ S)
    {x y : X} (h : x = y) (v : DottedTangentArrow f x) {K : Type u} [CommRing K]
    (e : X.residueField y ≃+* K) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫ (h ▸ v).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
        ((X.residueFieldCongr h).commRingCatIsoToRingEquiv.trans e)).toRingHom) ≫ v.val := by
  cases h
  rfl

/-- The bookkeeping half of `AlgebraicGeometry.pullbackLift_comp_mul_eq_add`, for an arbitrary
morphism `m` out of the fibre product which agrees with the first projection over the base. -/
private theorem pullbackLift_comp_eq_of_tangentMap {X S : Scheme.{u}} (p : X ⟶ S) (y : X)
    [IsIso (p.residueFieldMap y)] (z : ↑(pullback p p)) (m : pullback p p ⟶ X)
    (h₁ : pullback.fst p p z = y) (h₂ : pullback.snd p p z = y) (hm : m z = y)
    (hbase : m ≫ p = pullback.fst p p ≫ p)
    [IsIso (p.residueFieldMap (pullback.fst p p z))]
    [IsIso (p.residueFieldMap (pullback.snd p p z))]
    [IsIso ((pullback.fst p p).residueFieldMap z)] [IsIso ((pullback.snd p p).residueFieldMap z)]
    [IsIso (m.residueFieldMap z)]
    (v w : DottedTangentArrow p y) (t : Spec (.of (DualNumber (X.residueField y))) ⟶ X)
    (key : Spec.map (CommRingCat.ofHom (dualNumberCongr
        (X.residueFieldCongr hm).commRingCatIsoToRingEquiv).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr
        (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv.symm).toRingHom) ≫
      (liftTangentPair p p z (h₁.symm ▸ v) (h₂.symm ▸ w)).val ≫ m = t) :
    pullback.lift v.val w.val (v.property.2.trans w.property.2.symm) ≫ m = t := by
  rw [← key]
  let rC₁ := (X.residueFieldCongr h₁.symm).commRingCatIsoToRingEquiv
  let rC₂ := (X.residueFieldCongr h₂.symm).commRingCatIsoToRingEquiv
  let rM := (X.residueFieldCongr hm).commRingCatIsoToRingEquiv
  let em := (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv
  let qF := (asIso ((pullback.fst p p).residueFieldMap z)).commRingCatIsoToRingEquiv
  let qS := (asIso ((pullback.snd p p).residueFieldMap z)).commRingCatIsoToRingEquiv
  have hFS : rC₁.trans qF = rC₂.trans qS :=
    residueFieldCongr_trans_residueFieldMap_eq p (pullback.fst p p) (pullback.snd p p) z _
      pullback.condition h₁ h₂
  have hMF : rM.symm.trans em = rC₁.trans qF :=
    residueFieldCongr_trans_residueFieldMap_eq p m (pullback.fst p p) z _ hbase hm h₁
  have hlift : (liftTangentPair p p z (h₁.symm ▸ v) (h₂.symm ▸ w)).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr (rC₁.trans qF)).toRingHom) ≫
        pullback.lift v.val w.val (v.property.2.trans w.property.2.symm) := by
    apply pullback.hom_ext
    · simp only [liftTangentPair, firstFactorArrow, Category.assoc, pullback.lift_fst]
      exact specMap_comp_dottedTangentArrow_cast p h₁.symm v qF
    · simp only [liftTangentPair, secondFactorArrow, Category.assoc, pullback.lift_snd]
      rw [hFS]
      exact specMap_comp_dottedTangentArrow_cast p h₂.symm w qS
  have hid : (rM.symm.trans em).trans (em.symm.trans rM) = RingEquiv.refl _ :=
    RingEquiv.ext fun _ => by simp
  have hpre : (Spec.map (CommRingCat.ofHom (dualNumberCongr rM).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr em.symm).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr (rC₁.trans qF)).toRingHom) = 𝟙 _ := by
    rw [specMap_dualNumberCongr_comp, specMap_dualNumberCongr_comp, ← hMF, hid]
    exact Spec.map_id _
  rw [hlift]
  simp only [← Category.assoc] at hpre ⊢
  rw [hpre, Category.id_comp]

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)

/-- **The composition law of tangent vectors at the identity.** Two tangent vectors `v` and `w`
of `G/S` at the identity point over `s`, lifted to the fibre product `G ×_S G` and composed with
the multiplication, give the dual-number arrow of `v + w`. -/
theorem pullbackLift_comp_mul_eq_add (v w : DottedTangentArrow G.hom ((η[G]).left s)) :
    pullback.lift v.val w.val (v.property.2.trans w.property.2.symm) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left) =
      (v + w).val := by
  obtain ⟨h₁, h₂, hm, hbase, i₁, i₂, i₃, H⟩ := tangentMap_mul_at_identity G s
  have hcast : ∀ {x y : G.left} (h : x = y) (u : DottedTangentArrow G.hom x),
      (h ▸ u).val = Spec.map (CommRingCat.ofHom (dualNumberCongr
        (G.left.residueFieldCongr h).commRingCatIsoToRingEquiv).toRingHom) ≫ u.val := by
    intro x y h u
    cases h
    have hring : (dualNumberCongr
        (G.left.residueFieldCongr (rfl : x = x)).commRingCatIsoToRingEquiv).toRingHom =
        RingHom.id _ := RingHom.ext fun ⟨_, _⟩ => rfl
    change u.val = Spec.map (CommRingCat.ofHom (dualNumberCongr
      (G.left.residueFieldCongr (rfl : x = x)).commRingCatIsoToRingEquiv).toRingHom) ≫ u.val
    rw [hring]
    simp
  have key := congrArg Subtype.val (H v w)
  rw [hcast] at key
  have := i₁
  have := i₂
  have := i₃
  have : IsIso (G.hom.residueFieldMap ((η[G]).left s)) :=
    isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left (Over.Hom.w (η[G])) s
  let E := tangentSpaceProductEquiv G.hom G.hom
    ((Over.tensorObj_left G G) ▸ ((lift (η[G]) (η[G])).left s))
  have := E.fst_residueField_isIso
  have := E.snd_residueField_isIso
  rw [tangentMap_apply _ (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase _ _
    (dualNumberCongr (asIso (Scheme.Hom.residueFieldMap
      ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left)
      ((Over.tensorObj_left G G) ▸
        ((lift (η[G]) (η[G])).left s)))).commRingCatIsoToRingEquiv.symm).toRingHom
    (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)] at key
  have hP : E.toLinearEquiv.symm (h₁.symm ▸ v, h₂.symm ▸ w) =
      liftTangentPair G.hom G.hom _ (h₁.symm ▸ v) (h₂.symm ▸ w) := by
    apply E.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, E.toLinearEquiv_apply]
    exact (Prod.ext (tangentMap_fst_liftTangentPair _ _ _ _ _)
      (tangentMap_snd_liftTangentPair _ _ _ _ _)).symm
  rw [hP] at key
  exact pullbackLift_comp_eq_of_tangentMap G.hom _ _ _ h₁ h₂ hm hbase v w _ key

/-- A tangent vector at the identity followed by multiplication by `n + 1` is `n + 1` times the
tangent vector, as dual-number arrows. -/
theorem comp_pow_id_left_eq_nsmul (θ : DottedTangentArrow G.hom ((η[G]).left s)) (n : ℕ) :
    θ.val ≫ ((𝟙 G) ^ (n + 1)).left = ((n + 1) • θ).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left]
    have hc : θ.val ≫ pullback.lift ((𝟙 G) ^ (n + 1)).left (Over.Hom.left (𝟙 G))
        (by rw [Over.w, Over.w]) =
        pullback.lift ((n + 1) • θ).val θ.val
          (((n + 1) • θ).property.2.trans θ.property.2.symm) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ih]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Over.id_left, Category.comp_id]
    rw [← Category.assoc, hc, succ_nsmul _ (n + 1)]
    exact pullbackLift_comp_mul_eq_add G s _ _

/-- Multiplication by `d` fixes the unit section. -/
theorem unit_comp_zpow_id (d : ℤ) : η[G] ≫ (𝟙 G) ^ d = η[G] := by
  rw [GrpObj.comp_zpow, Category.comp_id, CategoryTheory.MonObj.one_eq_one, one_zpow]

/-- Multiplication by `d` fixes the unit section, on underlying schemes. -/
theorem unit_left_comp_zpow_id_left (d : ℤ) :
    (η[G]).left ≫ ((𝟙 G) ^ d).left = (η[G]).left := by
  rw [← Over.comp_left, unit_comp_zpow_id]

/-- Multiplication by `d` induces an isomorphism on the residue field of an identity point. -/
theorem isIso_residueFieldMap_zpow_id_left (d : ℤ) :
    IsIso (((𝟙 G) ^ d).left.residueFieldMap ((η[G]).left s)) := by
  have hη : (η[G]).left ≫ G.hom = 𝟙 S := Over.Hom.w (η[G])
  have hiso : ∀ {A B C D : CommRingCat} (c : A ≅ B) (x : B ⟶ D) [IsIso x] (a : A ⟶ C) (b : C ⟶ D),
      c.hom ≫ x = a ≫ b → (IsIso a → IsIso b) ∧ (IsIso b → IsIso a) := by
    intro A B C D c x _ a b h
    have := IsIso.comp_isIso' (Iso.isIso_hom c) ‹IsIso x›
    exact ⟨fun _ => IsIso.of_isIso_fac_left h.symm, fun _ => IsIso.of_isIso_fac_right h.symm⟩
  have h1 : IsIso ((η[G]).left.residueFieldMap s) := by
    have : IsIso (G.hom.residueFieldMap ((η[G]).left s)) :=
      isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left hη s
    have : IsIso (Scheme.Hom.residueFieldMap (𝟙 S) s) := by
      rw [Scheme.residueFieldMap_id]
      exact IsIso.id _
    have h := Scheme.residueFieldMap_comp (η[G]).left G.hom s
    rw [Scheme.Hom.residueFieldMap_congr hη s] at h
    exact (hiso _ _ _ _ h).1 ‹_›
  have h := Scheme.residueFieldMap_comp (η[G]).left ((𝟙 G) ^ d).left s
  rw [Scheme.Hom.residueFieldMap_congr (unit_left_comp_zpow_id_left G d) s] at h
  exact (hiso _ _ _ _ h).2 h1

/-- **The differential of multiplication by `n + 1` at an identity point is injective when
`n + 1` is invertible in the residue field there.** By the composition law of tangent vectors at
the identity, a tangent vector followed by multiplication by `n + 1` is `n + 1` times the
tangent vector. -/
theorem injective_tangentMap_pow_id_left (n : ℕ)
    (hn : IsUnit ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s))) :
    haveI := isIso_residueFieldMap_zpow_id_left G s ((n + 1 : ℕ) : ℤ)
    Function.Injective (tangentMap ((𝟙 G) ^ ((n + 1 : ℕ) : ℤ)).left G.hom G.hom (Over.w _)
      ((η[G]).left s)) := by
  have := isIso_residueFieldMap_zpow_id_left G s ((n + 1 : ℕ) : ℤ)
  intro v w hvw
  let φ := ((𝟙 G) ^ ((n + 1 : ℕ) : ℤ)).left
  let e := (asIso (φ.residueFieldMap ((η[G]).left s))).commRingCatIsoToRingEquiv
  let α := (dualNumberCongr e.symm).toRingHom
  have hT := fun u => tangentMap_apply φ G.hom G.hom (Over.w _) _ u α
    (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)
  have hval := congrArg Subtype.val hvw
  rw [hT, hT] at hval
  have : IsIso (CommRingCat.ofHom α) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (dualNumberCongr e.symm).bijective
  have hc := (cancel_epi (Spec.map (CommRingCat.ofHom α))).1 hval
  have hφ : φ = ((𝟙 G) ^ (n + 1)).left := by
    simp only [φ, zpow_natCast]
  rw [hφ, comp_pow_id_left_eq_nsmul, comp_pow_id_left_eq_nsmul] at hc
  have hsmul : ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s)) • v =
      ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s)) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact Subtype.ext hc
  exact hn.smul_left_cancel.1 hsmul

/-- **Multiplication by `n + 1` on a group scheme locally of finite type is unramified at an
identity point where `n + 1` is invertible in the residue field.** This is the tangent-space
criterion for unramifiedness at a point with unchanged residue field (Tag 0B2G) applied to
`injective_tangentMap_pow_id_left`. -/
theorem unramifiedAt_pow_id_left [LocallyOfFiniteType G.hom] (n : ℕ)
    (hn : IsUnit ((n + 1 : ℕ) : G.left.residueField ((η[G]).left s))) :
    UnramifiedAt ((𝟙 G) ^ ((n + 1 : ℕ) : ℤ)).left ((η[G]).left s) := by
  have := isIso_residueFieldMap_zpow_id_left G s ((n + 1 : ℕ) : ℤ)
  exact (injective_tangentMap_iff_unramifiedAt_of_locallyOfFiniteType_base _ G.hom G.hom _
    (Over.w _)).1 (injective_tangentMap_pow_id_left G s n hn)

end AlgebraicGeometry
