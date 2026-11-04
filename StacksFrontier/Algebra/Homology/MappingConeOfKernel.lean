module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso

/-!
# The mapping cone of a morphism whose cokernel is acyclic

Mathlib relates the mapping cone of the *monomorphism* of a short exact sequence of cochain
complexes to the third term of the sequence: `CochainComplex.mappingCone.descShortComplex` is a
quasi-isomorphism `mappingCone S.f ⟶ S.X₃` by
`CochainComplex.mappingCone.quasiIso_descShortComplex`. This file supplies the other half: it
relates the mapping cone of an arbitrary morphism to the *kernel* of that morphism, which for an
epimorphism is the dual statement.

Let `φ : K ⟶ L` be a morphism of cochain complexes in an abelian category, factored as
`K ⟶ M ⟶ L` with `0 → Z → K → M → 0` and `0 → M → L → Q → 0` short exact — so `Z` is the kernel
of `φ`, `M` its image and `Q` its cokernel. There is a short exact sequence of mapping cones

`0 ⟶ mappingCone (0 : Z ⟶ 0) ⟶ mappingCone φ ⟶ mappingCone (M ⟶ L) ⟶ 0`,

because degreewise it is the direct sum of `0 → Z → K → M → 0` in one degree and of the identity
of `L` in the next. Its third term has the homology of `Q`, by Mathlib's quasi-isomorphism above.
So in any degree `n` where `Q` has no homology in degrees `n` and `n - 1`, the first map is an
isomorphism on `H^n`: the cone of `φ` has, in that degree, the homology of the cone of `Z ⟶ 0`,
which is a shift of `Z`.

The complex `mappingCone (0 : Z ⟶ 0)` is used in place of `Z⟦1⟧` throughout: it is degreewise
isomorphic to it by `CochainComplex.mappingCone.isIso_inl_v`, and keeping it inside the mapping
cone API avoids the signs of the shift functor.

## Main definitions

* `CochainComplex.mappingCone.mapFromZero`: the morphism `mappingCone (0 : Z ⟶ 0) ⟶ mappingCone φ`
  attached to a morphism `a : Z ⟶ K` with `a ≫ φ = 0`.
* `CochainComplex.mappingCone.coneShortComplex`: the short complex of mapping cones displayed
  above.

## Main results

* `CochainComplex.mappingCone.shortExact_coneShortComplex`: that short complex is short exact.
* `CochainComplex.mappingCone.isZero_homology_mappingCone`: the cone of the monomorphism of a
  short exact sequence has no homology where the third term has none.
* `CochainComplex.mappingCone.isIso_homologyMap_mapFromZero`: **the main result**, that
  `mapFromZero` is an isomorphism on homology in a degree where the cokernel is acyclic.

## Implementation notes

The degreewise short exactness is proved from the four identities between `inl`, `inr`, `fst` and
`snd` and the extensionality principles `CochainComplex.mappingCone.ext_from` and
`CochainComplex.mappingCone.ext_to`, without unfolding the cone into a biproduct:

* the first map is a monomorphism because composing it with the isomorphism `inl` of the cone of
  `Z ⟶ 0` gives `a` followed by the split monomorphism `inl φ`, and `inl` has the first
  projection as a section there (`CochainComplex.mappingCone.fst_v_zero_comp_inl_v`), so the
  factor may be removed again without inverting anything;
* the second map is an epimorphism by `Preadditive.epi_iff_cancel_zero`: a morphism out of the
  cone of `M ⟶ L` killing it is zero on both components, on the `L` component because `inr` is
  carried to `inr`, and on the `M` component because `K ⟶ M` is an epimorphism;
* the first map is a kernel of the second: a morphism into `mappingCone φ` killed by the second
  map has zero `snd` component and its `fst` component is killed by `K ⟶ M`, hence factors
  through `Z` uniquely; `CochainComplex.mappingCone.id_X` reassembles it.

Each of these three is stated and proved for the two cone morphisms themselves, not for the
projections `(coneShortComplex _).f` and `(coneShortComplex _).g`, and the commutativity proof
`(b ≫ u) ≫ 𝟙 L = b ≫ u` of the second morphism is the named
`CochainComplex.mappingCone.comp_comp_id_comm` rather than a `by simp`. Both are needed for the
rewriting to go through: a goal in which the projections of `coneShortComplex` and the cones
themselves both occur is one in which the same object has two spellings that are equal only at
default transparency, which no `rw` and no instance search sees through; and an inlined
`Category.comp_id (b ≫ u)` puts the pattern `(b ≫ u) ≫ 𝟙 L` inside a proof argument, where
`rw [Category.assoc]` finds it and builds an ill-typed motive.

The last step of `isIso_homologyMap_mapFromZero` is the two-term argument of
`Stacks.Cotangent.isIso_homologyMap_f_of_isZero`, which is not available here: that lemma, though
general, lives in a file about the cotangent complex, which this file cannot import.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open scoped ZeroObject

universe v u

namespace CochainComplex.mappingCone

section Map

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {α : K₁ ⟶ K₂} {β : L₁ ⟶ L₂} (comm : φ₁ ≫ β = α ≫ φ₂)

/-- The left inclusion followed by the morphism of cones induced by a commutative square. -/
@[reassoc]
lemma inl_v_comp_map_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ₁).v p q hpq ≫ (map φ₁ φ₂ α β comm).f q = α.f p ≫ (inl φ₂).v p q hpq := by
  simp [map]

/-- The right inclusion followed by the morphism of cones induced by a commutative square. -/
@[reassoc]
lemma inr_f_comp_map_f (p : ℤ) :
    (inr φ₁).f p ≫ (map φ₁ φ₂ α β comm).f p = β.f p ≫ (inr φ₂).f p := by
  simp [map]

/-- The morphism of cones induced by a commutative square, followed by the first projection. -/
@[reassoc]
lemma map_f_comp_fst_v (p q : ℤ) (hpq : p + 1 = q) :
    (map φ₁ φ₂ α β comm).f p ≫ (fst φ₂).1.v p q hpq =
      (fst φ₁).1.v p q hpq ≫ α.f q := by
  refine ext_from φ₁ q p hpq ?_ ?_
  · simp [inl_v_comp_map_f_assoc]
  · simp [inr_f_comp_map_f_assoc]

/-- The morphism of cones induced by a commutative square, followed by the second projection. -/
@[reassoc]
lemma map_f_comp_snd_v (p : ℤ) :
    (map φ₁ φ₂ α β comm).f p ≫ (snd φ₂).v p p (add_zero p) =
      (snd φ₁).v p p (add_zero p) ≫ β.f p := by
  refine ext_from φ₁ (p + 1) p rfl ?_ ?_
  · simp [inl_v_comp_map_f_assoc]
  · simp [inr_f_comp_map_f_assoc]

end Map

section Kernel

variable {C : Type u} [Category.{v} C] [Abelian C]
  {Z K M L Q : CochainComplex C ℤ}

/-- The degree-`q` term of the zero complex is a zero object. -/
lemma isZero_zero_X (q : ℤ) : IsZero ((0 : CochainComplex C ℤ).X q) :=
  (HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero (isZero_zero _)

/-- The left inclusion of the cone of `Z ⟶ 0` is an isomorphism in every degree: the cone of a
morphism to the zero complex is a shift of its source. -/
instance isIso_inl_v_zero (p q : ℤ) (hpq : p + (-1) = q) :
    IsIso ((inl (0 : Z ⟶ (0 : CochainComplex C ℤ))).v p q hpq) :=
  isIso_inl_v _ p q hpq (isZero_zero_X q)

/-- **The morphism from the cone of `Z ⟶ 0` to the cone of `φ`** induced by a morphism
`a : Z ⟶ K` killed by `φ`. In degree `p - 1` it is `a` in degree `p`, landing in the `K` summand
of the cone. -/
def mapFromZero (a : Z ⟶ K) (φ : K ⟶ L) (h : a ≫ φ = 0) :
    mappingCone (0 : Z ⟶ (0 : CochainComplex C ℤ)) ⟶ mappingCone φ :=
  map _ φ a 0 (by simp [h])

/-- The left inclusion of the cone of `Z ⟶ 0` followed by `mapFromZero a φ h` is `a` followed by
the left inclusion of the cone of `φ`. -/
@[reassoc]
lemma inl_v_mapFromZero_f (a : Z ⟶ K) (φ : K ⟶ L) (h : a ≫ φ = 0)
    (p q : ℤ) (hpq : p + (-1) = q) :
    (inl (0 : Z ⟶ (0 : CochainComplex C ℤ))).v p q hpq ≫ (mapFromZero a φ h).f q =
      a.f p ≫ (inl φ).v p q hpq :=
  inl_v_comp_map_f _ p q hpq

/-- **The first projection of the cone of `Z ⟶ 0` is a section of its left inclusion.** The
second summand of that cone is a zero object, so the second term of
`CochainComplex.mappingCone.id_X` vanishes. -/
theorem fst_v_zero_comp_inl_v (p q : ℤ) (hpq : p + 1 = q) (hqp : q + (-1) = p) :
    (fst (0 : Z ⟶ (0 : CochainComplex C ℤ))).1.v p q hpq ≫
      (inl (0 : Z ⟶ (0 : CochainComplex C ℤ))).v q p hqp = 𝟙 _ := by
  have h := id_X (0 : Z ⟶ (0 : CochainComplex C ℤ)) p q hpq
  rwa [(isZero_zero_X p).eq_of_tgt
      ((snd (0 : Z ⟶ (0 : CochainComplex C ℤ))).v p p (add_zero p)) 0,
    zero_comp, add_zero] at h

variable (a : Z ⟶ K) (b : K ⟶ M) (u : M ⟶ L)

/-- The composite `a ≫ (b ≫ u)` vanishes as soon as `a ≫ b` does. -/
theorem comp_comp_eq_zero (hab : a ≫ b = 0) : a ≫ b ≫ u = 0 := by
  rw [← Category.assoc, hab, zero_comp]

/-- The commutative square exhibiting `b` as a morphism of cones from `b ≫ u` to `u`. -/
theorem comp_comp_id_comm : (b ≫ u) ≫ 𝟙 L = b ≫ u :=
  Category.comp_id _

/-- **Degreewise, the two maps of the short complex of cones compose to zero.** -/
theorem mapFromZero_f_comp_map_f (hab : a ≫ b = 0) (p : ℤ) :
    (mapFromZero a (b ≫ u) (comp_comp_eq_zero a b u hab)).f p ≫
        (map (b ≫ u) u b (𝟙 L) (comp_comp_id_comm b u)).f p = 0 := by
  refine ext_from _ (p + 1) p rfl ?_ ?_
  · rw [inl_v_mapFromZero_f_assoc, inl_v_comp_map_f, ← Category.assoc,
      ← HomologicalComplex.comp_f, hab]
    simp
  · exact (isZero_zero_X p).eq_of_src _ _

/-- **Degreewise, the first map of the short complex of cones is a monomorphism.** It is `a`
followed by the split monomorphism `inl`, read through the isomorphism `inl` of the cone of
`Z ⟶ 0`, whose inverse is the first projection. -/
theorem mono_mapFromZero_f (hab : a ≫ b = 0) (p : ℤ) (hmonoa : Mono (a.f (p + 1))) :
    Mono ((mapFromZero a (b ≫ u) (comp_comp_eq_zero a b u hab)).f p) := by
  have hinl : Mono ((inl (b ≫ u)).v (p + 1) p (add_neg_cancel_right p 1)) :=
    mono_of_mono_fac (inl_v_fst_v (b ≫ u) (p + 1) p rfl)
  rw [← mono_comp_iff_of_isIso ((inl (0 : Z ⟶ (0 : CochainComplex C ℤ))).v (p + 1) p
    (add_neg_cancel_right p 1)), inl_v_mapFromZero_f]
  exact mono_comp _ _

/-- **Degreewise, the second map of the short complex of cones is an epimorphism.** A morphism
out of the cone of `u` killing it vanishes on the `L` summand because `inr` is carried to `inr`,
and on the `M` summand because `b` is an epimorphism there. -/
theorem epi_map_f_of_epi (p : ℤ) (hepib : Epi (b.f (p + 1))) :
    Epi ((map (b ≫ u) u b (𝟙 L) (comp_comp_id_comm b u)).f p) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T w hw
  have h1 : (inl u).v (p + 1) p (add_neg_cancel_right p 1) ≫ w = 0 :=
    (cancel_epi (b.f (p + 1))).1 (by
      simpa [hw] using (inl_v_comp_map_f_assoc (comp_comp_id_comm b u) (p + 1) p
        (add_neg_cancel_right p 1) w).symm)
  have h2 : (inr u).f p ≫ w = 0 := by
    simpa [hw] using (inr_f_comp_map_f_assoc (comp_comp_id_comm b u) p w).symm
  refine ext_from u (p + 1) p rfl ?_ ?_
  · rw [h1, comp_zero]
  · rw [h2, comp_zero]

/-- **Degreewise, the first map of the short complex of cones is a kernel of the second.** A
morphism into the cone of `b ≫ u` killed by the second map has zero second component, and its
first component is killed by `b`, hence factors through `Z` uniquely;
`CochainComplex.mappingCone.id_X` reassembles it. -/
def isLimitKernelForkMapFromZero (hab : a ≫ b = 0) (p : ℤ)
    (hmonoa : Mono (a.f (p + 1)))
    (hker : IsLimit (KernelFork.ofι (a.f (p + 1))
      (show a.f (p + 1) ≫ b.f (p + 1) = 0 by
        rw [← HomologicalComplex.comp_f, hab]; simp))) :
    IsLimit (KernelFork.ofι ((mapFromZero a (b ≫ u) (comp_comp_eq_zero a b u hab)).f p)
      (mapFromZero_f_comp_map_f a b u hab p)) := by
  haveI := mono_mapFromZero_f a b u hab p hmonoa
  refine KernelFork.IsLimit.ofι' _ _ ?_
  intro T k hk
  have hsnd : k ≫ (snd (b ≫ u)).v p p (add_zero p) = 0 := by
    simpa [map_f_comp_snd_v] using hk =≫ (snd u).v p p (add_zero p)
  have hfst : (k ≫ (fst (b ≫ u)).1.v p (p + 1) rfl) ≫ b.f (p + 1) = 0 := by
    simpa [map_f_comp_fst_v] using hk =≫ (fst u).1.v p (p + 1) rfl
  obtain ⟨w, hw⟩ := KernelFork.IsLimit.lift' hker _ hfst
  refine ⟨w ≫ (inl (0 : Z ⟶ (0 : CochainComplex C ℤ))).v (p + 1) p
    (add_neg_cancel_right p 1), ?_⟩
  have hid : (fst (b ≫ u)).1.v p (p + 1) rfl ≫
      (inl (b ≫ u)).v (p + 1) p (add_neg_cancel_right p 1) =
      𝟙 _ - (snd (b ≫ u)).v p p (add_zero p) ≫ (inr (b ≫ u)).f p := by
    rw [eq_sub_iff_add_eq]
    exact id_X _ p (p + 1) rfl
  rw [Category.assoc, inl_v_mapFromZero_f, ← Category.assoc,
    show w ≫ a.f (p + 1) = k ≫ (fst (b ≫ u)).1.v p (p + 1) rfl from hw, Category.assoc,
    hid, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hsnd, zero_comp,
    sub_zero]

/-- **The short complex of mapping cones**
`cone (Z ⟶ 0) ⟶ cone (b ≫ u) ⟶ cone u`
attached to a composable pair `a : Z ⟶ K`, `b : K ⟶ M` with `a ≫ b = 0` and a morphism
`u : M ⟶ L`. -/
def coneShortComplex (hab : a ≫ b = 0) : ShortComplex (CochainComplex C ℤ) where
  X₁ := mappingCone (0 : Z ⟶ (0 : CochainComplex C ℤ))
  X₂ := mappingCone (b ≫ u)
  X₃ := mappingCone u
  f := mapFromZero a (b ≫ u) (comp_comp_eq_zero a b u hab)
  g := map (b ≫ u) u b (𝟙 L) (comp_comp_id_comm b u)
  zero := by
    ext p
    exact mapFromZero_f_comp_map_f a b u hab p

/-- **The short complex of mapping cones is short exact.** It is checked degreewise, where it is
the direct sum of `0 → Z → K → M → 0` in the next degree and of the identity of `L`. -/
theorem shortExact_coneShortComplex (hab : a ≫ b = 0)
    (h₁ : (ShortComplex.mk a b hab).ShortExact) :
    (coneShortComplex a b u hab).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 h₁ (p + 1)
  have := hdeg.mono_f
  have hmonoa : Mono (a.f (p + 1)) := hdeg.mono_f
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _
      (isLimitKernelForkMapFromZero a b u hab p hmonoa hdeg.exact.fIsKernel))
    (mono_mapFromZero_f a b u hab p hmonoa) (epi_map_f_of_epi b u p hdeg.epi_g)

/-- **The cone of the monomorphism of a short exact sequence has the homology of the third
term**: so where the third term has no homology, neither has the cone. This is Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex`, read as a vanishing statement. -/
theorem isZero_homology_mappingCone {pr : L ⟶ Q} (hupr : u ≫ pr = 0)
    (h₂ : (ShortComplex.mk u pr hupr).ShortExact) (n : ℤ) (hQ : IsZero (Q.homology n)) :
    IsZero ((mappingCone u).homology n) := by
  have : IsIso (HomologicalComplex.homologyMap
      (descShortComplex (ShortComplex.mk u pr hupr)) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 ((quasiIso_descShortComplex h₂).quasiIsoAt n)
  exact hQ.of_iso (asIso (HomologicalComplex.homologyMap
    (descShortComplex (ShortComplex.mk u pr hupr)) n))

/-- **The mapping cone of a morphism is the shift of its kernel, in a degree where its cokernel
is acyclic.** Let `φ = b ≫ u` with `0 → Z → K → M → 0` and `0 → M → L → Q → 0` short exact, so
that `Z` is the kernel of `φ` and `Q` its cokernel. If `Q` has no homology in the degrees `n` and
`n - 1`, then `CochainComplex.mappingCone.mapFromZero` is an isomorphism on homology in degree
`n`.

For an epimorphism `φ` — where `Q = 0` — this is the statement dual to Mathlib's
`CochainComplex.mappingCone.quasiIso_descShortComplex`. -/
theorem isIso_homologyMap_mapFromZero {φ : K ⟶ L} {pr : L ⟶ Q} (hφ : b ≫ u = φ)
    (hab : a ≫ b = 0) (hupr : u ≫ pr = 0)
    (h₁ : (ShortComplex.mk a b hab).ShortExact)
    (h₂ : (ShortComplex.mk u pr hupr).ShortExact) (n n' : ℤ) (hn : n' + 1 = n)
    (hQ : IsZero (Q.homology n)) (hQ' : IsZero (Q.homology n')) :
    IsIso (HomologicalComplex.homologyMap
      (mapFromZero a φ (by rw [← hφ, ← Category.assoc, hab, zero_comp])) n) := by
  subst hφ
  have hSE := shortExact_coneShortComplex a b u hab h₁
  have hmono : Mono (HomologicalComplex.homologyMap (coneShortComplex a b u hab).f n) :=
    (hSE.homology_exact₁ n' n hn).mono_g
      ((isZero_homology_mappingCone u hupr h₂ n' hQ').eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap (coneShortComplex a b u hab).f n) :=
    (hSE.homology_exact₂ n).epi_f ((isZero_homology_mappingCone u hupr h₂ n hQ).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (HomologicalComplex.homologyMap (coneShortComplex a b u hab).f n)

end Kernel

end CochainComplex.mappingCone

end
