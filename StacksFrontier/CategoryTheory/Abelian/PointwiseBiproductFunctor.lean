module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# The pointwise biproduct of two functors, and short complexes of biproduct shape

For two endofunctors `A` and `B` of an abelian category `C` we form the functor
`F ↦ A F ⊞ B F` and show that it is additive and exact as soon as `A` and `B` are.

We also record two cases of a Mayer--Vietoris shaped short complex `L ⟶ A ⊞ B ⟶ N`, with maps
`(a, -b)` and `(c, d)` for a commuting square `a ≫ c = b ≫ d`, which are short exact for formal
reasons: it suffices that one of the two maps out of the biproduct and the opposite map into it
be invertible.

## Main definitions

* `CategoryTheory.Functor.pointwiseBiprod`: the functor `F ↦ A F ⊞ B F`.
* `CategoryTheory.ShortComplex.biprodMayerVietoris`: the short complex `L ⟶ A ⊞ B ⟶ N` of a
  commuting square.

## Main results

* `CategoryTheory.Functor.pointwiseBiprod_preservesFiniteLimits` and
  `CategoryTheory.Functor.pointwiseBiprod_preservesFiniteColimits`: the pointwise biproduct of
  two exact functors is exact.
* `CategoryTheory.ShortComplex.shortExact_biprodMayerVietoris_of_isIso_fst` and
  `CategoryTheory.ShortComplex.shortExact_biprodMayerVietoris_of_isIso_snd`: the two formal
  short exactness criteria for a Mayer--Vietoris shaped short complex.
* `CategoryTheory.ShortComplex.shortExact_map_biprodMayerVietoris`: the image of a
  Mayer--Vietoris shaped short complex under an exact functor is short exact as soon as the
  Mayer--Vietoris short complex of the image square is.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A biproduct of two short exact sequences is short exact. -/
theorem shortExact_biprod_map {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    {f₁ : X₁ ⟶ X₂} {g₁ : X₂ ⟶ X₃} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {w₂ : f₂ ≫ g₂ = 0}
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact) :
    (ShortComplex.mk (biprod.map f₁ f₂) (biprod.map g₁ g₂)
      (by refine biprod.hom_ext _ _ ?_ ?_ <;> simp [w₁, w₂])).ShortExact := by
  have _ := h₁.mono_f
  have _ := h₂.mono_f
  have _ := h₁.epi_g
  have _ := h₂.epi_g
  refine { exact := ?_, mono_f := biprod.map_mono _ _, epi_g := biprod.map_epi _ _ }
  refine ((ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2 ⟨?_⟩).1
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} s hs ↦ biprod.lift
      (h₁.exact.lift (s ≫ biprod.fst) (by simpa using hs =≫ (biprod.fst : X₃ ⊞ Y₃ ⟶ X₃)))
      (h₂.exact.lift (s ≫ biprod.snd) (by simpa using hs =≫ (biprod.snd : X₃ ⊞ Y₃ ⟶ Y₃))))
    (fun {T} s hs ↦ ?_) (fun {T} s hs m hm ↦ ?_)
  · refine biprod.hom_ext _ _ ?_ ?_
    · simpa using h₁.exact.lift_f (s ≫ biprod.fst) _
    · simpa using h₂.exact.lift_f (s ≫ biprod.snd) _
  · refine biprod.hom_ext _ _ ?_ ?_
    · rw [biprod.lift_fst]
      refine (cancel_mono f₁).1 ?_
      rw [h₁.exact.lift_f]
      simpa using hm =≫ (biprod.fst : X₂ ⊞ Y₂ ⟶ X₂)
    · rw [biprod.lift_snd]
      refine (cancel_mono f₂).1 ?_
      rw [h₂.exact.lift_f]
      simpa using hm =≫ (biprod.snd : X₂ ⊞ Y₂ ⟶ Y₂)

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] (A B : C ⥤ C)

/-- The pointwise biproduct `F ↦ A F ⊞ B F` of two endofunctors of a category with binary
biproducts. -/
@[simps]
def pointwiseBiprod : C ⥤ C where
  obj F := A.obj F ⊞ B.obj F
  map φ := biprod.map (A.map φ) (B.map φ)
  map_id F := by ext <;> simp
  map_comp φ ψ := by ext <;> simp

/-- The transformation into a pointwise biproduct determined by its two components. -/
@[simps]
def pointwiseBiprod.lift {E : C ⥤ C} (τ : E ⟶ A) (σ : E ⟶ B) : E ⟶ pointwiseBiprod A B where
  app F := biprod.lift (τ.app F) (σ.app F)
  naturality F G φ := by
    change E.map φ ≫ biprod.lift (τ.app G) (σ.app G) =
      biprod.lift (τ.app F) (σ.app F) ≫ biprod.map (A.map φ) (B.map φ)
    refine biprod.hom_ext _ _ ?_ ?_
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact τ.naturality φ
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
      exact σ.naturality φ

/-- The transformation out of a pointwise biproduct determined by its two components. -/
@[simps]
def pointwiseBiprod.desc {E : C ⥤ C} (τ : A ⟶ E) (σ : B ⟶ E) : pointwiseBiprod A B ⟶ E where
  app F := biprod.desc (τ.app F) (σ.app F)
  naturality F G φ := by
    change biprod.map (A.map φ) (B.map φ) ≫ biprod.desc (τ.app G) (σ.app G) =
      biprod.desc (τ.app F) (σ.app F) ≫ E.map φ
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact τ.naturality φ
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      exact σ.naturality φ

variable [A.Additive] [B.Additive]

/-- The pointwise biproduct of two additive functors is additive. -/
instance pointwiseBiprod_additive : (pointwiseBiprod A B).Additive where
  map_add {X Y} φ ψ := by
    change biprod.map (A.map (φ + ψ)) (B.map (φ + ψ)) =
      biprod.map (A.map φ) (B.map φ) + biprod.map (A.map ψ) (B.map ψ)
    rw [A.map_add, B.map_add]
    refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [Preadditive.add_comp, Preadditive.comp_add]

variable [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- The pointwise biproduct of two exact functors takes a short exact sequence to a short exact
sequence. -/
theorem shortExact_map_pointwiseBiprod (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map (pointwiseBiprod A B)).ShortExact := by
  have hA := hS.map_of_exact A
  have hB := hS.map_of_exact B
  exact ShortComplex.shortExact_biprod_map
    (f₁ := A.map S.f) (g₁ := A.map S.g) (w₁ := (S.map A).zero)
    (f₂ := B.map S.f) (g₂ := B.map S.g) (w₂ := (S.map B).zero) hA hB

/-- The pointwise biproduct of two exact functors preserves finite limits. -/
instance pointwiseBiprod_preservesFiniteLimits :
    PreservesFiniteLimits (pointwiseBiprod A B) :=
  (preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun S hS ↦
    have h := shortExact_map_pointwiseBiprod A B S hS
    ⟨h.exact, h.mono_f⟩

/-- The pointwise biproduct of two exact functors preserves finite colimits. -/
instance pointwiseBiprod_preservesFiniteColimits :
    PreservesFiniteColimits (pointwiseBiprod A B) := by
  refine ((preservesFiniteColimits_tfae (pointwiseBiprod A B)).out 4 1).2 fun S hS ↦ ?_
  have h := shortExact_map_pointwiseBiprod A B S hS
  exact ⟨h.exact, h.epi_g⟩

end CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {L A B N : C}
  (a : L ⟶ A) (b : L ⟶ B) (c : A ⟶ N) (d : B ⟶ N) (h : a ≫ c = b ≫ d)

/-- The Mayer--Vietoris shaped short complex `L ⟶ A ⊞ B ⟶ N` attached to a commuting square,
with maps `(a, -b)` and `(c, d)`. -/
def biprodMayerVietoris : ShortComplex C :=
  ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c d) (by simp [h])

/-- The first map of `biprodMayerVietoris a b c d h` is `biprod.lift a (-b) : L ⟶ A ⊞ B`. -/
@[simp]
theorem biprodMayerVietoris_f : (biprodMayerVietoris a b c d h).f = biprod.lift a (-b) := rfl

/-- The second map of `biprodMayerVietoris a b c d h` is `biprod.desc c d : A ⊞ B ⟶ N`. -/
@[simp]
theorem biprodMayerVietoris_g : (biprodMayerVietoris a b c d h).g = biprod.desc c d := rfl

/-- A Mayer--Vietoris shaped short complex in which `c` and `b` are invertible is short exact. -/
theorem shortExact_biprodMayerVietoris_of_isIso_fst [IsIso c] [IsIso b] :
    (biprodMayerVietoris a b c d h).ShortExact := by
  let ψ : N ⊞ B ⟶ A ⊞ B := biprod.lift ((biprod.fst - biprod.snd ≫ d) ≫ inv c) biprod.snd
  let θ : A ⊞ B ⟶ N ⊞ B := biprod.lift (biprod.desc c d) biprod.snd
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [θ, ψ, Preadditive.sub_comp]
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [θ, ψ, Preadditive.sub_comp]
  let e : A ⊞ B ≅ N ⊞ B := ⟨θ, ψ, hθψ, hψθ⟩
  let S' : ShortComplex C :=
    ShortComplex.mk ((-b) ≫ (biprod.inr : B ⟶ N ⊞ B)) (biprod.fst : N ⊞ B ⟶ N) (by simp)
  have hsplit : S'.Splitting :=
    { r := biprod.snd ≫ (-(inv b))
      s := biprod.inl
      f_r := by simp [S']
      s_g := by simp [S']
      id := by rw [add_comm]; simp [S', biprod.total] }
  have hbd : b ≫ d ≫ inv c = a := by simp [← reassoc_of% h]
  refine ShortComplex.shortExact_of_iso
    (S₁ := S') (S₂ := biprodMayerVietoris a b c d h) ?_ hsplit.shortExact
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp [S', e, ψ, biprodMayerVietoris, Preadditive.comp_sub, hbd]
    · simp [S', e, ψ, biprodMayerVietoris]
  · simp only [S', e, ψ, biprodMayerVietoris, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      biprod.lift_desc, Preadditive.sub_comp, Category.assoc, IsIso.inv_hom_id]
    abel

/-- A Mayer--Vietoris shaped short complex in which `d` and `a` are invertible is short exact. -/
theorem shortExact_biprodMayerVietoris_of_isIso_snd [IsIso d] [IsIso a] :
    (biprodMayerVietoris a b c d h).ShortExact := by
  let ψ : A ⊞ N ⟶ A ⊞ B := biprod.lift biprod.fst ((biprod.snd - biprod.fst ≫ c) ≫ inv d)
  let θ : A ⊞ B ⟶ A ⊞ N := biprod.lift biprod.fst (biprod.desc c d)
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [θ, ψ, Preadditive.sub_comp]
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [θ, ψ, Preadditive.sub_comp]
  let e : A ⊞ B ≅ A ⊞ N := ⟨θ, ψ, hθψ, hψθ⟩
  let S' : ShortComplex C :=
    ShortComplex.mk (a ≫ (biprod.inl : A ⟶ A ⊞ N)) (biprod.snd : A ⊞ N ⟶ N) (by simp)
  have hsplit : S'.Splitting :=
    { r := biprod.fst ≫ inv a
      s := biprod.inr
      f_r := by simp [S']
      s_g := by simp [S']
      id := by simp [S', biprod.total] }
  have hac : a ≫ c ≫ inv d = b := by simp [reassoc_of% h]
  refine ShortComplex.shortExact_of_iso
    (S₁ := S') (S₂ := biprodMayerVietoris a b c d h) ?_ hsplit.shortExact
  refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
  · refine biprod.hom_ext _ _ ?_ ?_
    · simp [S', e, ψ, biprodMayerVietoris]
    · simp [S', e, ψ, biprodMayerVietoris, Preadditive.comp_sub, hac]
  · simp only [S', e, ψ, biprodMayerVietoris, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      biprod.lift_desc, Preadditive.sub_comp, Category.assoc, IsIso.inv_hom_id]
    abel

end CategoryTheory.ShortComplex

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {L A B N : C} (a : L ⟶ A) (b : L ⟶ B) (c : A ⟶ N) (d : B ⟶ N) (h : a ≫ c = b ≫ d)

omit [PreservesFiniteColimits F] in
/-- An exact functor sends a Mayer--Vietoris shaped short complex to a short complex which is
short exact as soon as the Mayer--Vietoris short complex of the image square is. -/
theorem shortExact_map_biprodMayerVietoris
    (hF : (biprodMayerVietoris (F.map a) (F.map b) (F.map c) (F.map d)
      (by rw [← F.map_comp, ← F.map_comp, h])).ShortExact) :
    ((biprodMayerVietoris a b c d h).map F).ShortExact := by
  have _ : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  refine ShortComplex.shortExact_of_iso
    (S₁ := biprodMayerVietoris (F.map a) (F.map b) (F.map c) (F.map d)
      (by rw [← F.map_comp, ← F.map_comp, h]))
    (S₂ := (biprodMayerVietoris a b c d h).map F) ?_ hF
  refine ShortComplex.isoMk (Iso.refl _) (F.mapBiprod A B).symm (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ F.map (biprod.lift a (-b)) =
      biprod.lift (F.map a) (-(F.map b)) ≫ (F.mapBiprod A B).inv
    rw [Category.id_comp, ← F.map_neg, biprod.lift_mapBiprod]
  · change (F.mapBiprod A B).inv ≫ F.map (biprod.desc c d) =
      biprod.desc (F.map c) (F.map d) ≫ 𝟙 _
    rw [Category.comp_id, biprod.mapBiprod_inv_map_desc]

end CategoryTheory.ShortComplex

end
