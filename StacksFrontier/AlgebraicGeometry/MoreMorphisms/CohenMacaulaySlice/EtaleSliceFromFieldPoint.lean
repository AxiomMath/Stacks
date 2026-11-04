module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.EtaleSliceThroughPoint
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.UnramifiedSlicePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularityTransfer

/-!
# An étale slice cut out by a field point of the base

Let `t : E ⟶ W` be smooth, let `s : E ⟶ U` be a morphism to an affine scheme, let `w ∈ W` and
let `κ(w) ⟶ K` be a field extension. Write `E_K = E_w ×_{κ(w)} K` for the fibre of `t` over the
field point `Spec K ⟶ W`. If the composite `E_K ⟶ E ⟶ U` is locally of finite type and
unramified at some point, then there are global functions `f₁, …, f_r` of `U` and an open
subscheme of `E ×_U V(f₁, …, f_r)` which is étale over `W` and contains a point over `w`.

## Main results

* `Stacks.AlgebraicGeometry.isRegular_iff_of_forall₂_units`: a regular sequence stays regular
  when its terms are multiplied by units.
* `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_generators_of_field`: a slice of a scheme over
  a field whose equations generate the maximal ideal at a point with finite separable residue
  field is unramified there.
* `Stacks.AlgebraicGeometry.exists_etale_slice_of_regular_fieldPoint`: an étale slice cut out by
  global functions whose germs form a regular system of generators of the maximal ideal of the
  local ring of `E_K` at a point with finite separable residue field.
* `Stacks.AlgebraicGeometry.exists_etale_slice_of_unramifiedAt_fieldPoint`: if `E_K ⟶ U` is
  locally of finite type and unramified at some point, some open subscheme of
  `E ×_U V(f₁, …, f_r)` is étale over `W` and contains a point over `w`.
* `Stacks.AlgebraicGeometry.exists_isOpenImmersion_surjective_pullback_opens`: the image of the
  slice in the zero scheme is open, and the slice surjects onto it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

section UnitMultiples

variable {R : Type*} [CommRing R]

/-- Multiplying the terms of a list by units does not change the ideal they generate. -/
theorem ofList_eq_of_forall₂_units {l l' : List R}
    (h : List.Forall₂ (fun a b : R => ∃ c : Rˣ, b = (c : R) * a) l l') :
    Ideal.ofList l = Ideal.ofList l' := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    obtain ⟨c, rfl⟩ := hab
    rw [Ideal.ofList_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit c.isUnit]

/-- If the terms of `l'` are unit multiples of those of `l` and `l` is a regular sequence, then
so is `l'`. -/
theorem isRegular_of_forall₂_units {l l' : List R}
    (h : List.Forall₂ (fun a b : R => ∃ c : Rˣ, b = (c : R) * a) l l')
    (H : RingTheory.Sequence.IsRegular R l) : RingTheory.Sequence.IsRegular R l' := by
  refine ⟨⟨fun i hi => ?_⟩, ?_⟩
  · have hi' : i < l.length := h.length_eq ▸ hi
    obtain ⟨c, hc⟩ := h.get hi' hi
    rw [← ofList_eq_of_forall₂_units (List.forall₂_take i h)]
    simp only [List.get_eq_getElem] at hc
    rw [hc]
    exact (Units.isSMulRegular _ c).mul (H.regular_mod_prev i hi')
  · rw [← ofList_eq_of_forall₂_units h]
    exact H.top_ne_smul

/-- **A regular sequence up to units.** Multiplying the terms of a list by units does not change
whether it is a regular sequence. -/
theorem isRegular_iff_of_forall₂_units {l l' : List R}
    (h : List.Forall₂ (fun a b : R => ∃ c : Rˣ, b = (c : R) * a) l l') :
    RingTheory.Sequence.IsRegular R l ↔ RingTheory.Sequence.IsRegular R l' := by
  refine ⟨isRegular_of_forall₂_units h, isRegular_of_forall₂_units ?_⟩
  refine List.Forall₂.flip (h.imp fun a b hab => ?_)
  obtain ⟨c, rfl⟩ := hab
  exact ⟨c⁻¹, by simp⟩

end UnitMultiples

/-- A point of a fibre is the point of the source it maps to, read in the fibre over its image:
any property of pairs (point of the base, point of the fibre over it) transfers from `(y, a)` to
`(t (t.fiberι y a), t.asFiber (t.fiberι y a))`. -/
theorem fiber_transport {X Y : Scheme.{u}} (t : X ⟶ Y) (Pr : ∀ y : Y, t.fiber y → Prop)
    {y : Y} (a : t.fiber y) (h : Pr y a) :
    Pr (t (t.fiberι y a)) (t.asFiber (t.fiberι y a)) := by
  have happ : ∀ (y : Y) (a : t.fiber y), t (t.fiberι y a) = y := fun y a => by
    simpa using (t.range_fiberι y).subset ⟨a, rfl⟩
  have hinj : ∀ p q : Σ y, t.fiber y, t.fiberι p.1 p.2 = t.fiberι q.1 q.2 → p = q := by
    rintro ⟨y₁, a₁⟩ ⟨y₂, a₂⟩ hpq
    have h12 : y₁ = y₂ := by rw [← happ y₁ a₁, ← happ y₂ a₂]; exact congrArg t hpq
    subst h12
    simp only at hpq
    rw [(t.fiberι y₁).isEmbedding.injective hpq]
  have key := hinj ⟨y, a⟩ ⟨t (t.fiberι y a), t.asFiber (t.fiberι y a)⟩
    (t.fiberι_asFiber _).symm
  have h' : (fun p : Σ y, t.fiber y => Pr p.1 p.2) ⟨y, a⟩ := h
  rwa [key] at h'

/-- The germ of a global section, transported along an equality of points, is the germ at the
other point. -/
theorem stalkCongr_germ_top {X : Scheme.{u}} {a b : X} (h : a = b) (y : Γ(X, ⊤)) :
    (X.presheaf.stalkCongr (.of_eq h)).hom (X.presheaf.germ ⊤ a trivial y) =
      X.presheaf.germ ⊤ b trivial y := by
  subst h
  simp

/-- **Unramifiedness of a slice over a field (Stacks 02GF, (7)).** Let `g : V ⟶ Spec K` and let
`ψ : Z ⟶ V` be surjective on stalks and kill global functions `F₁, …, F_r` of `V` whose germs
generate the maximal ideal of `𝒪_{V, ψ z}`. If `κ(ψ z)/K` is finite separable, then `ψ ≫ g` is
unramified at `z`. -/
theorem unramifiedAt_comp_of_generators_of_field {Z V : Scheme.{u}} {K : Type u} [Field K]
    (ψ : Z ⟶ V) [SurjectiveOnStalks ψ] (g : V ⟶ Spec (.of K)) [LocallyOfFiniteType (ψ ≫ g)]
    {r : ℕ} (F : Fin r → Γ(V, ⊤)) (hvan : ∀ i, ψ.appTop (F i) = 0) (z : Z)
    (hmax : Ideal.ofList (List.ofFn fun i => V.presheaf.germ ⊤ (ψ z) trivial (F i)) =
      maximalIdeal (V.presheaf.stalk (ψ z)))
    (hsep : letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ V.Γevaluation (ψ z)).hom.toAlgebra
      Module.Finite K (V.residueField (ψ z)) ∧ Algebra.IsSeparable K (V.residueField (ψ z))) :
    UnramifiedAt (ψ ≫ g) z := by
  have hψsurj : Function.Surjective (ψ.stalkMap z).hom := ψ.stalkMap_surjective z
  have hbot : maximalIdeal (Z.presheaf.stalk z) = ⊥ := by
    rw [← map_maximalIdeal_of_surjective _ hψsurj, ← hmax, Ideal.map_ofList, List.map_ofFn,
      eq_bot_iff, Ideal.ofList, Ideal.span_le]
    intro y hy
    simp only [Set.mem_setOf_eq, List.mem_ofFn] at hy
    obtain ⟨i, rfl⟩ := hy
    simp only [Function.comp_apply, SetLike.mem_coe, Ideal.mem_bot]
    exact (Scheme.Hom.germ_stalkMap_apply ψ ⊤ z trivial (F i)).trans <|
      (congrArg (fun y => (Z.presheaf.germ (ψ ⁻¹ᵁ ⊤) z trivial).hom y) (hvan i)).trans
        (map_zero _)
  have hA : Ideal.map ((ψ ≫ g).stalkMap z).hom
      (maximalIdeal ((Spec (.of K)).presheaf.stalk ((ψ ≫ g) z))) =
      maximalIdeal (Z.presheaf.stalk z) :=
    le_antisymm (by rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]) (hbot ▸ bot_le)
  have hγ : Function.Bijective (ψ.residueFieldMap z).hom := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨c, rfl⟩ := Z.residue_surjective z y
    obtain ⟨b, rfl⟩ := hψsurj c
    exact ⟨V.residue (ψ z) b,
      by simpa using congrArg (fun φ => φ.hom b) (Scheme.residue_residueFieldMap ψ z)⟩
  have hρ : let := (g.residueFieldMap (ψ z)).hom.toAlgebra
      Module.Finite ((Spec (.of K)).residueField (g (ψ z))) (V.residueField (ψ z)) ∧
        Algebra.IsSeparable ((Spec (.of K)).residueField (g (ψ z))) (V.residueField (ψ z)) := by
    let : Algebra K ((Spec (.of K)).residueField (g (ψ z))) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation (g (ψ z))).hom.toAlgebra
    let : Algebra ((Spec (.of K)).residueField (g (ψ z))) (V.residueField (ψ z)) :=
      (g.residueFieldMap (ψ z)).hom.toAlgebra
    let : Algebra K (V.residueField (ψ z)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop ≫ V.Γevaluation (ψ z)).hom.toAlgebra
    have : IsScalarTower K ((Spec (.of K)).residueField (g (ψ z))) (V.residueField (ψ z)) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        have h := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of K)).inv.hom x))
          (Scheme.Γevaluation_naturality g (ψ z))
        simpa [RingHom.algebraMap_toAlgebra] using h.symm
    have h1 : Module.Finite K (V.residueField (ψ z)) := hsep.1
    have h2 : Algebra.IsSeparable K (V.residueField (ψ z)) := hsep.2
    exact ⟨Module.Finite.of_restrictScalars_finite K _ _,
      Algebra.isSeparable_tower_top_of_isSeparable K _ _⟩
  have hB : let := ((ψ ≫ g).residueFieldMap z).hom.toAlgebra
      Module.Finite ((Spec (.of K)).residueField ((ψ ≫ g) z)) (Z.residueField z) ∧
        Algebra.IsSeparable ((Spec (.of K)).residueField ((ψ ≫ g) z)) (Z.residueField z) := by
    rw [Scheme.residueFieldMap_comp ψ g z]
    exact finite_isSeparable_comp_of_bijective _ _ hγ hρ
  exact ((unramifiedAt_tfae (ψ ≫ g) z).out 7 1).1 (And.intro hA hB)

/-- The projection of the fibre over a field point to the field is smooth when `t` is. -/
private theorem smooth_snd_fiberToSpecResidueField {E W : Scheme.{u}} (t : E ⟶ W) [Smooth t]
    (w : W) {K : Type u} [Field K] (φ : W.residueField w ⟶ CommRingCat.of K) :
    Smooth (pullback.snd (t.fiberToSpecResidueField w) (Spec.map φ)) :=
  have : Smooth (t.fiberToSpecResidueField w) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback t (W.fromSpecResidueField w)) ‹Smooth t›
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback (t.fiberToSpecResidueField w) (Spec.map φ)) inferInstance

/-- **An étale slice from a regular sequence in the fibre over a field point.** Let
`t : E ⟶ W` be smooth, `s : E ⟶ U` with `U` affine, `w ∈ W`, `φ : κ(w) ⟶ K` a field extension
and `v` a point of `E_K = E_w ×_{κ(w)} K` whose residue field is finite separable over `K`. If
`f₁, …, f_d` in the maximal ideal of `𝒪_{U, v}` map to generators of the maximal ideal of
`𝒪_{E_K, v}` forming a regular sequence, then there are global functions of `U` and an open
subscheme of `E ×_U V(f₁, …, f_r)` which is étale over `W` and contains a point lying over
`w`. -/
theorem exists_etale_slice_of_regular_fieldPoint
    {E U W : Scheme.{u}} [IsAffine U] (s : E ⟶ U) (t : E ⟶ W) [Smooth t]
    (w : W) {K : Type u} [Field K] (φ : W.residueField w ⟶ CommRingCat.of K)
    (v : ↥(pullback (t.fiberToSpecResidueField w) (Spec.map φ)))
    (hsep : letI := ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd (t.fiberToSpecResidueField w) (Spec.map φ)).appTop ≫
        (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).Γevaluation v).hom.toAlgebra
      Module.Finite K ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField v) ∧
        Algebra.IsSeparable K
          ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField v))
    (xs : List (U.presheaf.stalk
      ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s) v)))
    (hxm : ∀ x ∈ xs, x ∈ maximalIdeal (U.presheaf.stalk
      ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s) v)))
    (hgen : Ideal.ofList (xs.map
        ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s).stalkMap
          v).hom) =
      maximalIdeal ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v))
    (hreg : RingTheory.Sequence.IsRegular
      ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v)
      (xs.map ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫
        s).stalkMap v).hom)) :
    ∃ (r : ℕ) (f : Fin r → Γ(U, ⊤)) (P : Scheme.{u})
      (p : P ⟶ pullback s
        (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f))).subschemeι),
      IsOpenImmersion p ∧ Etale (p ≫ pullback.fst _ _ ≫ t) ∧
        ∃ x : P, (p ≫ pullback.fst _ _ ≫ t) x = w := by
  revert xs hxm hgen hreg
  set pV : pullback (t.fiberToSpecResidueField w) (Spec.map φ) ⟶ t.fiber w := pullback.fst _ _
    with hpV
  set gV : pullback (t.fiberToSpecResidueField w) (Spec.map φ) ⟶ Spec (.of K) :=
    pullback.snd _ _ with hgV
  set φV := pV ≫ t.fiberι w ≫ s with hφVdef
  intro xs hxm hgen hreg
  have : Smooth gV := smooth_snd_fiberToSpecResidueField t w φ
  have : Flat (Spec.map φ) := flat_SpecMap_of_residueField φ
  have : Flat pV := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback (t.fiberToSpecResidueField w) (Spec.map φ)).flip inferInstance
  let : Algebra Γ(U, ⊤) (U.presheaf.stalk (φV v)) :=
    (U.presheaf.germ ⊤ (φV v) trivial).hom.toAlgebra
  have hloc := (isAffineOpen_top U).isLocalization_stalk ⟨φV v, trivial⟩
  have key : ∀ y : U.presheaf.stalk (φV v), ∃ a b : Γ(U, ⊤),
      IsUnit (U.presheaf.germ ⊤ (φV v) trivial b) ∧
        y * U.presheaf.germ ⊤ (φV v) trivial b = U.presheaf.germ ⊤ (φV v) trivial a := by
    intro y
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj
      ((isAffineOpen_top U).primeIdealOf ⟨φV v, trivial⟩).asIdeal.primeCompl y
    exact ⟨a, b, IsLocalization.map_units _ b, h⟩
  choose a b hb hab using key
  let f : Fin xs.length → Γ(U, ⊤) := fun i => a (xs.get i)
  have hgermφ : ∀ y : Γ(U, ⊤), (φV.stalkMap v).hom (U.presheaf.germ ⊤ (φV v) trivial y) =
      (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.germ ⊤ v trivial
        (φV.appTop y) := fun y => Scheme.Hom.germ_stalkMap_apply φV ⊤ v trivial y
  set gs := List.ofFn fun i => (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.germ
    ⊤ v trivial (φV.appTop (f i)) with hgs
  have hrel : List.Forall₂
      (fun x y : (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v =>
        ∃ c : ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v)ˣ,
          y = (c : _) * x)
      (xs.map (φV.stalkMap v).hom) gs := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [gs], fun i h₁ h₂ => ?_⟩
    have hi : i < xs.length := by simpa using h₁
    refine ⟨((hb (xs[i]'hi)).map (φV.stalkMap v).hom).unit, ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map, gs, List.getElem_ofFn, f]
    rw [IsUnit.unit_spec, ← hgermφ, ← hab, map_mul, mul_comm]
  have hreg' := (isRegular_iff_of_forall₂_units hrel).1 hreg
  have hgen' : Ideal.ofList gs = _ := (ofList_eq_of_forall₂_units hrel).symm.trans hgen
  set rs := List.ofFn fun i => ((t.fiberι w).stalkMap (pV v)).hom
    (E.presheaf.germ ⊤ (t.fiberι w (pV v)) trivial (s.appTop (f i))) with hrs
  have hmap : rs.map (pV.stalkMap v).hom = gs := by
    simp only [rs, gs, List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, φV, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
    rw [Scheme.Hom.germ_stalkMap_apply (t.fiberι w) ⊤ (pV v) trivial,
      Scheme.Hom.germ_stalkMap_apply pV ((t.fiberι w) ⁻¹ᵁ ⊤) v (by simp)]
    rfl
  have hregE : RingTheory.Sequence.IsRegular _ rs :=
    (isRegular_map_stalkMap_iff pV v rs).1 (hmap ▸ hreg')
  have hregular := fiber_transport t (fun y a => RingTheory.Sequence.IsRegular
      ((t.fiber y).presheaf.stalk a) (List.ofFn fun i => ((t.fiberι y).stalkMap a).hom
        (E.presheaf.germ ⊤ (t.fiberι y a) trivial (s.appTop (f i))))) (pV v) hregE
  set e := t.fiberι w (pV v) with he
  have hregular' : RingTheory.Sequence.IsRegular ((t.fiber (t e)).presheaf.stalk (t.asFiber e))
      (List.ofFn fun i : Fin xs.length => ((t.fiberι (t e)).stalkMap (t.asFiber e)).hom
        ((t.fiberι_asFiber e).symm ▸ E.presheaf.germ ⊤ e trivial (s.appTop (f i)))) := by
    convert hregular using 3
    rw [← stalkCongr_hom_eq_rec, stalkCongr_germ_top]
    exact (t.fiberι_asFiber e).symm
  set I := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f)) with hI
  have hsupp : φV v ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_ofIdealTop,
      Scheme.mem_zeroLocus_iff]
    intro y hy hyb
    have hle : Ideal.ofList (List.ofFn f) ≤
        (maximalIdeal (U.presheaf.stalk (φV v))).comap (U.presheaf.germ ⊤ (φV v) trivial).hom := by
      rw [Ideal.ofList, Ideal.span_le]
      intro c hc
      simp only [Set.mem_setOf_eq, List.mem_ofFn] at hc
      obtain ⟨i, rfl⟩ := hc
      simp only [SetLike.mem_coe, Ideal.mem_comap, f, ← hab]
      exact Ideal.mul_mem_right _ _ (hxm _ (List.get_mem _ _))
    have hy' := hle hy
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hy'
    exact hy' ((Scheme.mem_basicOpen U y (φV v) trivial).1 hyb)
  obtain ⟨y₀, hy₀⟩ := hsupp
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φV) (g := I.subschemeι)
    v y₀ hy₀.symm
  have hφV : φV = (pV ≫ t.fiberι w) ≫ s := by simp [φV]
  let zY : pullback φV I.subschemeι ⟶ pullback s I.subschemeι :=
    pullback.lift (pullback.fst _ _ ≫ pV ≫ t.fiberι w) (pullback.snd _ _)
      (by rw [Category.assoc, ← hφV, pullback.condition])
  have sqA : IsPullback (pV ≫ t.fiberι w) gV t (Spec.map φ ≫ W.fromSpecResidueField w) :=
    (IsPullback.of_hasPullback (t.fiberToSpecResidueField w) (Spec.map φ)).paste_horiz
      (IsPullback.of_hasPullback t (W.fromSpecResidueField w))
  have sqB : IsPullback zY (pullback.fst φV I.subschemeι) (pullback.fst s I.subschemeι)
      (pV ≫ t.fiberι w) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd s I.subschemeι) (v₁₃ := I.subschemeι)
      (h₂₂ := s) ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback s I.subschemeι).flip
    rw [pullback.lift_snd, ← hφV]
    exact (IsPullback.of_hasPullback φV I.subschemeι).flip
  have sq := sqB.paste_vert sqA
  have hvan : ∀ i, (pullback.fst φV I.subschemeι).appTop (φV.appTop (f i)) = 0 := by
    intro i
    have h0 : I.subschemeι.appTop (f i) = 0 := by
      show f i ∈ RingHom.ker (I.subschemeι.app ⊤).hom
      rw [I.ker_subschemeι_app ⟨⊤, isAffineOpen_top U⟩, hI,
        Scheme.IdealSheafData.ofIdealTop_ideal]
      convert Ideal.mem_map_of_mem _
        (Ideal.subset_span (show f i ∈ {x | x ∈ List.ofFn f} from List.mem_ofFn.2 ⟨i, rfl⟩))
      simp
    have hc := congrArg (fun k => k.appTop (f i)) (pullback.condition (f := φV) (g := I.subschemeι))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc
    rw [hc, h0, map_zero]
  have hgenz : Ideal.ofList (List.ofFn fun i =>
      (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.germ ⊤
        (pullback.fst φV I.subschemeι z) trivial (φV.appTop (f i))) =
      maximalIdeal ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk
        (pullback.fst φV I.subschemeι z)) := by
    rw [hz₁]; exact hgen'
  have hsepz : let := ((Scheme.ΓSpecIso (.of K)).inv ≫ gV.appTop ≫
      (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).Γevaluation
        (pullback.fst φV I.subschemeι z)).hom.toAlgebra
      Module.Finite K ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField
          (pullback.fst φV I.subschemeι z)) ∧
        Algebra.IsSeparable K ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField
          (pullback.fst φV I.subschemeι z)) := by
    rw [hz₁]; exact hsep
  have hunrZ : UnramifiedAt (pullback.fst φV I.subschemeι ≫ gV) z :=
    unramifiedAt_comp_of_generators_of_field _ gV (fun i => φV.appTop (f i)) hvan z hgenz hsepz
  have hunrY := (unramifiedAt_isPullback_iff sq z).1 hunrZ
  have he' : pullback.fst s I.subschemeι (zY z) = e := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hz₁]
    rfl
  obtain ⟨P, p, hp, ⟨x, hx⟩, het⟩ := exists_isOpenImmersion_etale_pullback_zeroScheme s t e
    ((Flat.iff_flat_stalkMap t).mp inferInstance e) f hregular' I hI (zY z) he' hunrY
  refine ⟨xs.length, f, P, p, hp, het, x, ?_⟩
  simp only [Scheme.Hom.comp_apply]
  rw [hx, he', he]
  simpa using (t.range_fiberι w).subset ⟨pV _, rfl⟩

/-- **An étale slice from a point of the fibre over a field point.** Let `t : E ⟶ W` be
smooth, `s : E ⟶ U` with `U` affine, `w ∈ W`, `φ : κ(w) ⟶ K` a field extension and `v` a point
of `E_K = E_w ×_{κ(w)} K` whose residue field is finite separable over `K`, at which the maximal
ideal of `𝒪_{U, v}` generates the maximal ideal of `𝒪_{E_K, v}`. Then there are global
functions `f₁, …, f_r` of `U` and an open subscheme of `E ×_U V(f₁, …, f_r)` which is étale over
`W` and contains a point lying over `w`. -/
theorem exists_etale_slice_of_map_maximalIdeal_fieldPoint
    {E U W : Scheme.{u}} [IsAffine U] (s : E ⟶ U) (t : E ⟶ W) [Smooth t]
    (w : W) {K : Type u} [Field K] (φ : W.residueField w ⟶ CommRingCat.of K)
    (v : ↥(pullback (t.fiberToSpecResidueField w) (Spec.map φ)))
    (hsep : letI := ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd (t.fiberToSpecResidueField w) (Spec.map φ)).appTop ≫
        (pullback (t.fiberToSpecResidueField w) (Spec.map φ)).Γevaluation v).hom.toAlgebra
      Module.Finite K ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField v) ∧
        Algebra.IsSeparable K
          ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).residueField v))
    (hmap : Ideal.map
        ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s).stalkMap
          v).hom (maximalIdeal (U.presheaf.stalk
            ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s) v))) =
      maximalIdeal ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v)) :
    ∃ (r : ℕ) (f : Fin r → Γ(U, ⊤)) (P : Scheme.{u})
      (p : P ⟶ pullback s
        (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f))).subschemeι),
      IsOpenImmersion p ∧ Etale (p ≫ pullback.fst _ _ ≫ t) ∧
        ∃ x : P, (p ≫ pullback.fst _ _ ≫ t) x = w := by
  have := smooth_snd_fiberToSpecResidueField t w φ
  have hregL : IsRegularLocalRing
      ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk v) :=
    (isRegular_of_smooth_over_field
      (pullback.snd (t.fiberToSpecResidueField w) (Spec.map φ))).isRegularLocalRing_stalk v
  obtain ⟨xs, hxs, hlen, hgen⟩ := IsLocalRing.exists_list_map_eq_maximalIdeal _ hmap
  have hlen' : (xs.map ((pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫
      t.fiberι w ≫ s).stalkMap v).hom).length =
      (maximalIdeal ((pullback (t.fiberToSpecResidueField w) (Spec.map φ)).presheaf.stalk
        v)).spanFinrank := by
    rw [List.length_map, hlen]
  exact exists_etale_slice_of_regular_fieldPoint s t w φ v hsep xs hxs hgen
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      _).1 _ hgen hlen').1

/-- **An étale slice from a field point of the base.** Let `t : E ⟶ W` be smooth, `s : E ⟶ U`
with `U` affine, `w ∈ W` and `φ : κ(w) ⟶ K` a field extension. If the composite
`E_w ×_{κ(w)} K ⟶ E ⟶ U` is locally of finite type and unramified at some point, then there are
global functions `f₁, …, f_r` of `U` and an open subscheme of `E ×_U V(f₁, …, f_r)` which is
étale over `W` and contains a point lying over `w`. -/
theorem exists_etale_slice_of_unramifiedAt_fieldPoint
    {E U W : Scheme.{u}} [IsAffine U] (s : E ⟶ U) (t : E ⟶ W) [Smooth t]
    (w : W) {K : Type u} [Field K] (φ : W.residueField w ⟶ CommRingCat.of K)
    [LocallyOfFiniteType
      (pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s)]
    (v₀ : ↥(pullback (t.fiberToSpecResidueField w) (Spec.map φ)))
    (hv₀ : UnramifiedAt
      (pullback.fst (t.fiberToSpecResidueField w) (Spec.map φ) ≫ t.fiberι w ≫ s) v₀) :
    ∃ (r : ℕ) (f : Fin r → Γ(U, ⊤)) (P : Scheme.{u})
      (p : P ⟶ pullback s
        (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f))).subschemeι),
      IsOpenImmersion p ∧ Etale (p ≫ pullback.fst _ _ ≫ t) ∧
        ∃ x : P, (p ≫ pullback.fst _ _ ≫ t) x = w := by
  set pV : pullback (t.fiberToSpecResidueField w) (Spec.map φ) ⟶ t.fiber w := pullback.fst _ _
    with hpV
  set gV : pullback (t.fiberToSpecResidueField w) (Spec.map φ) ⟶ Spec (.of K) :=
    pullback.snd _ _ with hgV
  set φV := pV ≫ t.fiberι w ≫ s with hφVdef
  have : Smooth gV := smooth_snd_fiberToSpecResidueField t w φ
  obtain ⟨v, -, hsep, xs, hxm, -, hgen, hreg⟩ :=
    exists_closedPoint_regular_slice_of_smooth_of_unramifiedAt gV φV v₀ hv₀
  exact exists_etale_slice_of_regular_fieldPoint s t w φ v hsep xs hxm hgen hreg

/-- **The image of an open piece of a base change along a universally open morphism.** Let
`s : E ⟶ U` be universally open, `ι : Y ⟶ U` any morphism and `p : P ⟶ E ×_U Y` an open
immersion. Then the image `O` of `P` in `Y` is open, and `p` factors through an open immersion
`P ⟶ E ×_U O` whose composite to `O` is surjective. -/
theorem exists_isOpenImmersion_surjective_pullback_opens {E U Y P : Scheme.{u}} (s : E ⟶ U)
    [UniversallyOpen s] (ι : Y ⟶ U) (p : P ⟶ pullback s ι) [IsOpenImmersion p] :
    ∃ (O : Y.Opens) (p' : P ⟶ pullback s (O.ι ≫ ι)),
      IsOpenImmersion p' ∧ Function.Surjective (p' ≫ pullback.snd s (O.ι ≫ ι)) ∧
        p' ≫ pullback.lift (pullback.fst s (O.ι ≫ ι)) (pullback.snd s (O.ι ≫ ι) ≫ O.ι)
          (by rw [pullback.condition, Category.assoc]) = p := by
  have : UniversallyOpen (pullback.snd s ι) :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) (IsPullback.of_hasPullback s ι) ‹_›
  have hopen : IsOpenMap (p ≫ pullback.snd s ι) :=
    (pullback.snd s ι).isOpenMap.comp p.isOpenEmbedding.isOpenMap
  let O : Y.Opens := ⟨Set.range (p ≫ pullback.snd s ι), hopen.isOpen_range⟩
  have hfac : Set.range (p ≫ pullback.snd s ι) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_rfl
  let q : P ⟶ O := IsOpenImmersion.lift O.ι (p ≫ pullback.snd s ι) hfac
  have hq : q ≫ O.ι = p ≫ pullback.snd s ι := IsOpenImmersion.lift_fac _ _ _
  let m : pullback s (O.ι ≫ ι) ⟶ pullback s ι :=
    pullback.lift (pullback.fst s (O.ι ≫ ι)) (pullback.snd s (O.ι ≫ ι) ≫ O.ι)
      (by rw [pullback.condition, Category.assoc])
  let p' : P ⟶ pullback s (O.ι ≫ ι) := pullback.lift (p ≫ pullback.fst s ι) q
    (by rw [Category.assoc, pullback.condition, ← Category.assoc q, hq, Category.assoc])
  have hp' : p' ≫ m = p := by
    apply pullback.hom_ext
    · simp only [m, p', Category.assoc, pullback.lift_fst]
    · simp only [m, p', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hq]
  have sq : IsPullback m (pullback.snd s (O.ι ≫ ι)) (pullback.snd s ι) O.ι := by
    refine IsPullback.of_right (h₁₂ := pullback.fst s ι) (v₁₃ := s) (h₂₂ := ι) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s ι)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback s (O.ι ≫ ι)
  have : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have : IsOpenImmersion (p' ≫ m) := by rw [hp']; infer_instance
  refine ⟨O, p', IsOpenImmersion.of_comp p' m, fun o => ?_, hp'⟩
  obtain ⟨x, hx⟩ := o.2
  refine ⟨x, O.ι.isOpenEmbedding.injective ?_⟩
  show (p' ≫ pullback.snd s (O.ι ≫ ι) ≫ O.ι) x = O.ι o
  rwa [pullback.lift_snd_assoc, hq]

end Stacks.AlgebraicGeometry

end
