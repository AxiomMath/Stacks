module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelLocalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PolarGeometricInput
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ResidueFunctionIntegral

/-!
# Sections of the divisor cut out by an element, near the codimension-one points

Let `(A, 𝔪)` be a two-dimensional Noetherian normal local domain, `f : X ⟶ Spec A` a
modification with `X` normal, `c ∈ A` nonzero and `Z ⊂ X` the closed subscheme cut out by `c`,
whose structure sheaf is `𝒪_X / c𝒪_X` (`AlgebraicGeometry.zeroSchemeStructureSheaf`).

A global section `s` of `𝒪_Z` is, near every point `x`, the image of a function `t_x` on `X`.
The rational functions `t_x / c` satisfy the hypotheses of the polar lemma
`AlgebraicGeometry.forall_mem_stalkSubring_of_polar_of_isModification` as soon as `s` vanishes
near the codimension-one points of `X` not over the closed point, so they are regular, and `s`
vanishes. This is the injectivity of [Stacks, Tag 0AXB] in the form used by
[Stacks, Tag 0AXJ].

## Main results

* `AlgebraicGeometry.ZeroScheme.exists_lift`: local lifts of sections of `𝒪_Z`.
* `AlgebraicGeometry.ZeroScheme.residue`: the value in `κ(y)` of a section of `𝒪_Z`, at a point
  `y` where `c` vanishes.
* `AlgebraicGeometry.ZeroScheme.eq_zero_of_forall_coheight_eq_one`: a section of `𝒪_Z` whose
  local lifts are divisible by `c` at the codimension-one points not over the closed point is
  zero.

## References

* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing Order

universe u

namespace AlgebraicGeometry.ZeroScheme

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (c : A)

/-- The function `c` restricted to an open of `X`. -/
abbrev baseRes (W : X.Opens) : Γ(X, W) :=
  X.presheaf.map (homOfLE le_top).op (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) c)

/-- Sections of `𝒪_Z` over an open. -/
abbrev Sec (W : X.Opens) : Type u :=
  (zeroSchemeStructureSheaf X f c).val.obj (op W)

/-- The quotient map `Γ(W, 𝒪_X) ⟶ Γ(W, 𝒪_Z)`. -/
def proj (W : X.Opens) (t : Γ(X, W)) : Sec f c W :=
  (toZeroSchemeStructureSheaf X f c).val.app (op W) t

/-- Restriction of sections of `𝒪_Z`. -/
def resZ {W V : X.Opens} (h : W ≤ V) (s : Sec f c V) : Sec f c W :=
  (zeroSchemeStructureSheaf X f c).val.map (homOfLE h).op s

/-- The germ of `c` at a point is the image of `c` in the local ring. -/
lemma germ_baseRes (W : X.Opens) (x : X) (hx : x ∈ W) :
    X.presheaf.germ W x hx (baseRes f c W) = baseRingToStalk f x c := by
  rw [baseRes, TopCat.Presheaf.germ_res_apply, CommRingCat.comp_apply]
  exact (Scheme.Hom.germ_stalkMap_apply f ⊤ x (Set.mem_univ _) _).symm

/-- Every section of `𝒪_Z` is, near each point of its domain, the image of a function on `X`. -/
theorem exists_lift {V : X.Opens} (s : Sec f c V) {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (h : W ≤ V) (t : Γ(X, W)), x ∈ W ∧ proj f c W t = resZ f c h s :=
  Stacks.SheafOfModules.exists_cokernel_π_eq _ s hx

/-- A function on `X` whose image in `𝒪_Z` vanishes is, near each point, divisible by `c`. -/
theorem exists_eq_mul_of_proj_eq_zero {V : X.Opens} (t : Γ(X, V)) (ht : proj f c V t = 0)
    {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (h : W ≤ V) (r : Γ(X, W)), x ∈ W ∧
      baseRes f c W * r = X.presheaf.map (homOfLE h).op t :=
  Stacks.SheafOfModules.exists_eq_of_cokernel_π_eq_zero
    (baseSmulModules X f c (SheafOfModules.unit X.ringCatSheaf)) (V := V) t ht hx

/-- Multiples of `c` vanish in `𝒪_Z`. -/
lemma proj_baseRes_mul (W : X.Opens) (r : Γ(X, W)) : proj f c W (baseRes f c W * r) = 0 := by
  have h := congrArg (fun φ => φ.val.app (op W) r)
    (cokernel.condition (baseSmulModules X f c (SheafOfModules.unit X.ringCatSheaf)))
  exact h

/-- The quotient map commutes with restriction. -/
lemma proj_map {W V : X.Opens} (h : W ≤ V) (t : Γ(X, V)) :
    proj f c W (X.presheaf.map (homOfLE h).op t) = resZ f c h (proj f c V t) :=
  PresheafOfModules.naturality_apply (toZeroSchemeStructureSheaf X f c).val (homOfLE h).op t

/-- The quotient map is additive. -/
lemma proj_sub (W : X.Opens) (t t' : Γ(X, W)) :
    proj f c W (t - t') = proj f c W t - proj f c W t' :=
  map_sub ((toZeroSchemeStructureSheaf X f c).val.app (op W)).hom t t'

/-- Restriction of sections of `𝒪_Z` is functorial. -/
lemma resZ_resZ {W' W V : X.Opens} (h' : W' ≤ W) (h : W ≤ V) (s : Sec f c V) :
    resZ f c h' (resZ f c h s) = resZ f c (h'.trans h) s := by
  simp only [resZ]
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Two functions with the same image in `𝒪_Z` near a point `y` have germs at `y` differing by
`c` times a germ. -/
theorem exists_germ_sub_eq_mul {V V' : X.Opens} {T : X.Opens} (s : Sec f c T) {y : X}
    (hy : y ∈ V) (hy' : y ∈ V') (hV : V ≤ T) (hV' : V' ≤ T) (t : Γ(X, V)) (t' : Γ(X, V'))
    (ht : proj f c V t = resZ f c hV s) (ht' : proj f c V' t' = resZ f c hV' s) :
    ∃ g : X.presheaf.stalk y,
      X.presheaf.germ V y hy t - X.presheaf.germ V' y hy' t' = baseRingToStalk f y c * g := by
  set W := V ⊓ V'
  let u : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op t -
    X.presheaf.map (homOfLE inf_le_right).op t'
  have hu : proj f c W u = 0 := by
    rw [proj_sub, proj_map, proj_map, ht, ht', resZ_resZ, resZ_resZ, sub_self]
  obtain ⟨W', h, r, hyW', hr⟩ := exists_eq_mul_of_proj_eq_zero f c u hu ⟨hy, hy'⟩
  refine ⟨X.presheaf.germ W' y hyW' r, ?_⟩
  have h1 := congrArg (X.presheaf.germ W' y hyW') hr
  rw [map_mul, germ_baseRes, TopCat.Presheaf.germ_res_apply, map_sub,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1
  exact h1.symm

variable {f c} in
/-- At a point where `c` vanishes, two local lifts of a section of `𝒪_Z` have the same residue. -/
theorem residue_germ_eq {V V' : X.Opens} {T : X.Opens} (s : Sec f c T) {y : X}
    (hc : baseRingToStalk f y c ∈ maximalIdeal (X.presheaf.stalk y))
    (hy : y ∈ V) (hy' : y ∈ V') (hV : V ≤ T) (hV' : V' ≤ T) (t : Γ(X, V)) (t' : Γ(X, V'))
    (ht : proj f c V t = resZ f c hV s) (ht' : proj f c V' t' = resZ f c hV' s) :
    X.residue y (X.presheaf.germ V y hy t) = X.residue y (X.presheaf.germ V' y hy' t') := by
  obtain ⟨g, hg⟩ := exists_germ_sub_eq_mul f c s hy hy' hV hV' t t' ht ht'
  rw [← sub_eq_zero, ← map_sub, hg]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (Ideal.mul_mem_right _ _ hc)

/-- A chosen local lift of a global section of `𝒪_Z` near a point. -/
def liftOpen (s : Sec f c ⊤) (y : X) : X.Opens :=
  (exists_lift f c s (Set.mem_univ y)).choose

/-- The point lies in the domain of the chosen lift. -/
lemma mem_liftOpen (s : Sec f c ⊤) (y : X) : y ∈ liftOpen f c s y :=
  (exists_lift f c s (Set.mem_univ y)).choose_spec.choose_spec.choose_spec.1

/-- The chosen local lift itself. -/
def lift (s : Sec f c ⊤) (y : X) : Γ(X, liftOpen f c s y) :=
  (exists_lift f c s (Set.mem_univ y)).choose_spec.choose_spec.choose

/-- The chosen lift lifts the section. -/
lemma proj_lift (s : Sec f c ⊤) (y : X) :
    proj f c _ (lift f c s y) = resZ f c le_top s :=
  (exists_lift f c s (Set.mem_univ y)).choose_spec.choose_spec.choose_spec.2

/-- The value of a global section of `𝒪_Z` in the residue field at a point: the residue of the
germ of a local lift. It does not depend on the lift where `c` vanishes. -/
def residue (s : Sec f c ⊤) (y : X) : X.residueField y :=
  X.residue y (X.presheaf.germ _ y (mem_liftOpen f c s y) (lift f c s y))

variable {f c} in
/-- The residue of a section of `𝒪_Z` where `c` vanishes, computed from any local lift. -/
lemma residue_eq {s : Sec f c ⊤} {y : X}
    (hc : baseRingToStalk f y c ∈ maximalIdeal (X.presheaf.stalk y)) {V : X.Opens} (hy : y ∈ V)
    (t : Γ(X, V)) (ht : proj f c V t = resZ f c le_top s) :
    residue f c s y = X.residue y (X.presheaf.germ V y hy t) :=
  residue_germ_eq s hc _ hy le_top le_top _ t (proj_lift f c s y) ht

/-- Restriction of functions is functorial. -/
lemma map_map {W' W V : X.Opens} (h' : W' ≤ W) (h : W ≤ V) (t : Γ(X, V)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (h'.trans h)).op t := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- A section of `𝒪_Z` vanishing near every point of its domain vanishes. -/
lemma eq_zero_of_locally {V : X.Opens} (s : Sec f c V)
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧ resZ f c hW s = 0) : s = 0 :=
  Stacks.SheafOfModules.eq_zero_of_locally_zero' (zeroSchemeStructureSheaf X f c) s
    fun x hx => by
      obtain ⟨W, hW, hxW, h0⟩ := h x hx
      exact ⟨W, homOfLE hW, hxW, h0⟩

section Polar

variable [IsIntegral X]

/-- The image in the function field of a germ is the germ at the generic point. -/
lemma algebraMap_germ (W : X.Opens) (x : X) (hx : x ∈ W) (t : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx t) =
      X.presheaf.germ W (genericPoint X) ((genericPoint_spec X).specializes trivial |>.mem_open
        W.isOpen hx) t := by
  show X.presheaf.stalkSpecializes _ (X.presheaf.germ W x hx t) = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx _ t

/-- The germ of `c` at the generic point is its image in the function field. -/
lemma germ_genericPoint_baseRes (W : X.Opens) (hη : genericPoint X ∈ W) :
    X.presheaf.germ W (genericPoint X) hη (baseRes f c W) = baseFun f c :=
  germ_baseRes f c W _ hη

variable {f c} in
/-- The divisibility criterion: if a function on `X` equals `c r` near `y`, then its quotient
by `c` lies in `𝒪_{X, y}`. -/
lemma mem_stalkSubring_of_eq_mul {V : X.Opens} (t : Γ(X, V)) (hη : genericPoint X ∈ V) {y : X}
    {W : X.Opens} (hW : W ≤ V) (hyW : y ∈ W) (r : Γ(X, W))
    (hr : baseRes f c W * r = X.presheaf.map (homOfLE hW).op t) (hc : baseFun f c ≠ 0) :
    X.presheaf.germ V (genericPoint X) hη t * (baseFun f c)⁻¹ ∈ stalkSubring y := by
  have hηW : genericPoint X ∈ W := (genericPoint_specializes y).mem_open W.isOpen hyW
  have h1 := congrArg (X.presheaf.germ W (genericPoint X) hηW) hr
  rw [map_mul, germ_genericPoint_baseRes, TopCat.Presheaf.germ_res_apply] at h1
  refine ⟨X.presheaf.germ W y hyW r, ?_⟩
  rw [algebraMap_germ, ← h1]
  field_simp

variable [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsNormal X]

/-- **Sections of `𝒪_Z` are determined near the codimension-one points not over the closed
point.** Let `A` be a two-dimensional Noetherian normal local domain, `f : X ⟶ Spec A` a
modification with `X` normal and `c ∈ A` nonzero. A global section of `𝒪_X / c𝒪_X` which
vanishes near each codimension-one point of `X` not over the closed point is zero. -/
theorem eq_zero_of_forall_coheight_eq_one (hdim : ringKrullDim A = 2) (hf : IsModification f)
    (hc : c ≠ 0) (s : Sec f c ⊤)
    (hs : ∀ y : X, coheight y = 1 → f y ≠ closedPoint A →
      ∃ (W : X.Opens), y ∈ W ∧ resZ f c (le_top : W ≤ ⊤) s = 0) :
    s = 0 := by
  have hc' : baseFun f c ≠ 0 := baseFun_ne_zero hdim f hf hc
  have hη : ∀ x, genericPoint X ∈ liftOpen f c s x := fun x =>
    (genericPoint_specializes x).mem_open (liftOpen f c s x).isOpen (mem_liftOpen f c s x)
  let h : X → X.functionField := fun x =>
    X.presheaf.germ _ (genericPoint X) (hη x) (lift f c s x) * (baseFun f c)⁻¹
  have hreg := forall_mem_stalkSubring_of_polar_of_isModification hdim f hf h
    (fun y hy1 hfy => by
      obtain ⟨W, hyW, hW0⟩ := hs y hy1 hfy
      have hu : proj f c (W ⊓ liftOpen f c s y)
          (X.presheaf.map (homOfLE inf_le_right).op (lift f c s y)) = 0 := by
        rw [proj_map, proj_lift, resZ_resZ,
          show (inf_le_right.trans le_top : W ⊓ liftOpen f c s y ≤ ⊤) =
            (inf_le_left.trans le_top) from rfl, ← resZ_resZ f c inf_le_left le_top, hW0]
        exact map_zero _
      obtain ⟨W', hW', r, hyW', hr⟩ := exists_eq_mul_of_proj_eq_zero f c _ hu
        ⟨hyW, mem_liftOpen f c s y⟩
      refine mem_stalkSubring_of_eq_mul (lift f c s y) (hη y) (hW'.trans inf_le_right) hyW' r ?_ hc'
      rw [hr, map_map])
    (fun x => by
      refine ⟨liftOpen f c s x, mem_liftOpen f c s x, fun y hy => ?_⟩
      obtain ⟨g, hg⟩ := exists_germ_sub_eq_mul f c s hy (mem_liftOpen f c s y) le_top le_top
        (lift f c s x) (lift f c s y) (proj_lift f c s x) (proj_lift f c s y)
      refine ⟨g, ?_⟩
      have h1 := congrArg (algebraMap (X.presheaf.stalk y) X.functionField) hg
      rw [map_sub, map_mul, algebraMap_germ, algebraMap_germ, algebraMap_baseRingToStalk] at h1
      simp only [h, ← sub_mul, h1]
      field_simp)
  refine eq_zero_of_locally f c s fun x _ => ?_
  obtain ⟨u, hu⟩ := hreg x
  have h2 : X.presheaf.germ _ x (mem_liftOpen f c s x) (lift f c s x) =
      baseRingToStalk f x c * u := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, algebraMap_baseRingToStalk, hu, algebraMap_germ]
    simp only [h]
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hc', mul_one]
  obtain ⟨W1, hxW1, v, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf u
  rw [← germ_baseRes f c W1 x hxW1, ← map_mul] at h2
  obtain ⟨W2, hxW2, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf x _ hxW1 _ _ h2
  refine ⟨W2, le_top, hxW2, ?_⟩
  have h3 := congrArg (proj f c W2) he
  rwa [show iU = homOfLE iU.le from rfl, proj_map, proj_lift, resZ_resZ, map_mul,
    show iV = homOfLE iV.le from rfl, baseRes, map_map, ← baseRes, proj_baseRes_mul] at h3

end Polar

end AlgebraicGeometry.ZeroScheme
