module

public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans

/-!
# Dévissage for a morphism of exact functors that need not commute with the shift

`StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated` extends the invertibility of a
morphism `τ : F ⟶ G` of exact direct-sum-preserving functors from a compact generating family to
every object, but it asks `τ` to be compatible with the shift, `NatTrans.CommShift τ ℤ`: that is
what makes `τ` a morphism of triangles and lets the five lemma for triangles apply.

This file removes that hypothesis. The class of objects `K` at which `τ` is invertible at *every
shift* `K⟦n⟧` is closed under extensions in distinguished triangles for an arbitrary natural
transformation between exact functors: the five lemma is run on the long exact sequences of
morphism groups `Hom(M, F(-))` and `Hom(M, G(-))` attached to a distinguished triangle and its
rotation, whose connecting maps are images of morphisms of the source category and are therefore
respected by `τ` by naturality alone. The price is that invertibility is asked for at all shifts
of the generators, rather than at the generators only.

## Main results

* `StacksDraft.CompactDevissage.isIso_app_obj₃_of_isIso_shift` — the five lemma for an arbitrary
  natural transformation: invertibility at `X₁`, `X₂`, `X₁⟦1⟧` and `X₂⟦1⟧` gives invertibility at
  `X₃` for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`.
* `StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift` — the
  dévissage: invertibility at every shift of every member of a compact generating family gives
  invertibility everywhere.

## References

* [The Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty

namespace StacksDraft.CompactDevissage

open StacksDraft.NatTransDevissage

universe v v' u u'

section Triangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {F G : D ⥤ D'} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (τ : F ⟶ G)

/-- Exactness of `Hom(M, F(-))` at the third vertex of a distinguished triangle. -/
lemma exists_comp_map_mor₂_of_comp_map_mor₃ (T : Triangle D) (hT : T ∈ distTriang D) {M : D'}
    (u : M ⟶ F.obj T.obj₃) (hu : u ≫ F.map T.mor₃ = 0) :
    ∃ w : M ⟶ F.obj T.obj₂, u = w ≫ F.map T.mor₂ :=
  Triangle.coyoneda_exact₃
    (Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
      (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁))
    (F.map_distinguished T hT) u (by rw [Triangle.mk_mor₃, reassoc_of% hu, zero_comp])

/-- Exactness of `Hom(M, F(-))` at the second vertex of a distinguished triangle. -/
lemma exists_comp_map_mor₁_of_comp_map_mor₂ (T : Triangle D) (hT : T ∈ distTriang D) {M : D'}
    (u : M ⟶ F.obj T.obj₂) (hu : u ≫ F.map T.mor₂ = 0) :
    ∃ v : M ⟶ F.obj T.obj₁, u = v ≫ F.map T.mor₁ :=
  Triangle.coyoneda_exact₂ _ (F.map_distinguished T hT) u hu

/-- Exactness of `Hom(M, F(-))` at the shift of the first vertex of a distinguished triangle,
read on the rotated triangle. -/
lemma exists_comp_map_mor₃_of_comp_map_shift (T : Triangle D) (hT : T ∈ distTriang D) {M : D'}
    (u : M ⟶ F.obj (T.obj₁⟦(1 : ℤ)⟧)) (hu : u ≫ F.map (T.mor₁⟦(1 : ℤ)⟧') = 0) :
    ∃ v : M ⟶ F.obj T.obj₃, u = v ≫ F.map T.mor₃ :=
  Triangle.coyoneda_exact₃
    (Triangle.mk (F.map T.mor₂) (F.map T.mor₃)
      (F.map (-T.mor₁⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₂))
    (F.map_distinguished _ (rot_of_distTriang T hT)) u
    (by rw [Triangle.mk_mor₃, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      reassoc_of% hu, zero_comp, neg_zero])

/-- **The five lemma for an arbitrary morphism of exact functors.** Let `τ : F ⟶ G` be a
morphism of exact functors, not assumed to commute with the shift, and let
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be distinguished. If `τ` is invertible at `X₁`, `X₂`, `X₁⟦1⟧` and
`X₂⟦1⟧`, it is invertible at `X₃`.

The proof is the five lemma on the sequences of morphism groups out of a test object, whose
connecting maps are `F` and `G` applied to morphisms of `D`, so that `τ` commutes with them by
naturality. -/
lemma isIso_app_obj₃_of_isIso_shift (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : IsIso (τ.app T.obj₁)) (h₂ : IsIso (τ.app T.obj₂))
    (h₁' : IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧))) (h₂' : IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧))) :
    IsIso (τ.app T.obj₃) := by
  refine isIso_of_yoneda_map_bijective _ fun M => ⟨fun x x' hxx' => ?_, fun y => ?_⟩
  · -- injectivity, through the difference of the two preimages
    rw [← sub_eq_zero]
    have hx : (x - x') ≫ τ.app T.obj₃ = 0 := by
      dsimp only at hxx'
      rw [Preadditive.sub_comp, hxx', sub_self]
    set x₀ := x - x'
    have hx₀ : x₀ ≫ F.map T.mor₃ = 0 := by
      rw [← cancel_mono (τ.app (T.obj₁⟦(1 : ℤ)⟧)), Category.assoc, τ.naturality,
        reassoc_of% hx, zero_comp, zero_comp]
    obtain ⟨w, hw₀⟩ := exists_comp_map_mor₂_of_comp_map_mor₃ T hT x₀ hx₀
    rw [hw₀] at hx ⊢
    have hw : (w ≫ τ.app T.obj₂) ≫ G.map T.mor₂ = 0 := by
      rw [Category.assoc, ← τ.naturality, ← Category.assoc, hx]
    obtain ⟨v, hv⟩ := exists_comp_map_mor₁_of_comp_map_mor₂ T hT (F := G) _ hw
    have hw' : w = (v ≫ inv (τ.app T.obj₁)) ≫ F.map T.mor₁ := by
      rw [← cancel_mono (τ.app T.obj₂), hv, Category.assoc, Category.assoc, τ.naturality,
        IsIso.inv_hom_id_assoc]
    rw [hw', Category.assoc, ← F.map_comp, comp_distTriang_mor_zero₁₂ T hT, F.map_zero,
      comp_zero]
  · -- surjectivity, by correcting a first preimage
    have hz : (y ≫ G.map T.mor₃ ≫ inv (τ.app (T.obj₁⟦(1 : ℤ)⟧))) ≫
        F.map (T.mor₁⟦(1 : ℤ)⟧') = 0 := by
      rw [← cancel_mono (τ.app (T.obj₂⟦(1 : ℤ)⟧)), Category.assoc, Category.assoc,
        Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc, ← G.map_comp,
        comp_distTriang_mor_zero₃₁ T hT, G.map_zero, comp_zero, zero_comp]
    obtain ⟨v, hv⟩ := exists_comp_map_mor₃_of_comp_map_shift T hT _ hz
    have hd : (y - v ≫ τ.app T.obj₃) ≫ G.map T.mor₃ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← τ.naturality, ← Category.assoc, ← hv,
        Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id, sub_self]
    obtain ⟨w, hw⟩ := exists_comp_map_mor₂_of_comp_map_mor₃ (F := G) T hT _ hd
    refine ⟨v + (w ≫ inv (τ.app T.obj₂)) ≫ F.map T.mor₂, ?_⟩
    dsimp only
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, τ.naturality,
      IsIso.inv_hom_id_assoc, ← hw, add_sub_cancel]

/-- The objects at every shift of which `τ` is invertible. -/
def isoLocus : ObjectProperty D := fun K => ∀ n : ℤ, IsIso (τ.app (K⟦n⟧))

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- The class `isoLocus τ` is closed under isomorphisms. -/
lemma isoLocus_of_iso {K K' : D} (e : K ≅ K') (hK : isoLocus τ K) : isoLocus τ K' :=
  fun n => isIso_app_of_iso τ ((shiftFunctor D n).mapIso e) (hK n)

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- The class `isoLocus τ` is closed under shifts. -/
lemma isoLocus_shift {K : D} (hK : isoLocus τ K) (m : ℤ) : isoLocus τ (K⟦m⟧) :=
  fun n => isIso_app_of_iso τ ((shiftFunctorAdd D m n).app K) (hK (m + n))

/-- **The class `isoLocus τ` is closed under extensions.** -/
lemma isoLocus_obj₃ (T : Triangle D) (hT : T ∈ distTriang D) (h₁ : isoLocus τ T.obj₁)
    (h₂ : isoLocus τ T.obj₂) : isoLocus τ T.obj₃ := fun n =>
  isIso_app_obj₃_of_isIso_shift τ _ (Triangle.shift_distinguished T hT n) (h₁ n) (h₂ n)
    (isoLocus_shift τ h₁ n 1) (isoLocus_shift τ h₂ n 1)

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- The class `isoLocus τ` is closed under the direct sums that `F` and `G` preserve. -/
lemma isoLocus_of_isColimit {J : Type*} [PreservesColimitsOfShape (Discrete J) F]
    [PreservesColimitsOfShape (Discrete J) G] (Z : Discrete J ⥤ D) {c : Cocone Z}
    (hc : IsColimit c) (h : ∀ j, isoLocus τ (Z.obj j)) : isoLocus τ c.pt := fun n => by
  have hc' := isColimitOfPreserves (shiftFunctor D n) hc
  exact isIso_app_of_isColimit τ (Z ⋙ shiftFunctor D n) hc' fun j => h j n

/-- **The dévissage, for a morphism of exact functors that need not commute with the shift.** Let
`D` be a pre-triangulated category with direct sums generated by a family `E` of compact objects,
and let `F, G : D ⥤ D'` be exact functors preserving those direct sums. A morphism `τ : F ⟶ G`
which is invertible at every shift of every `E i` is invertible at every object of `D`. -/
theorem isIso_app_of_isCompactlyGenerated_of_forall_shift [HasCoproducts.{v} D]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G] {ι : Type v}
    (E : ι → D) (hEc : ∀ i, IsCompactObject.{v} (E i))
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y)
    (hτ : ∀ i (n : ℤ), IsIso (τ.app ((E i)⟦n⟧))) (X : D) : IsIso (τ.app X) := by
  have := hEc
  have hbase : ∀ Y, (⨆ J : Type v, ((ofObj E).shiftClosure ℤ).colimitsOfShape (Discrete J)) Y →
      isoLocus τ Y := by
    intro Y hY
    rw [ObjectProperty.prop_iSup_iff] at hY
    obtain ⟨J, ⟨p⟩⟩ := hY
    refine isoLocus_of_isColimit τ p.diag p.isColimit fun j => ?_
    obtain ⟨W, m, e, ⟨i⟩⟩ := p.prop_diag_obj j
    exact isoLocus_of_iso τ e.symm (isoLocus_shift τ (fun n => hτ i n) m)
  obtain ⟨W, hcolim, h₀, hstep⟩ :=
    Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated E hE X
  have hW : ∀ n : ℕ, isoLocus τ (W.obj n) := by
    intro n
    induction n with
    | zero => exact hbase _ h₀
    | succ n ih =>
        obtain ⟨Y, hY, f, g, hT⟩ := hstep n
        exact isoLocus_obj₃ τ (Triangle.mk f (W.map (homOfLE (Nat.le_succ n))) g) hT
          (hbase _ hY) ih
  obtain ⟨p, q, hT⟩ := hcolim
  have : PreservesColimitsOfShape (Discrete ℕ) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) F
  have : PreservesColimitsOfShape (Discrete ℕ) G :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) G
  have hsum : isoLocus τ (∐ W.obj) :=
    isoLocus_of_isColimit τ (Discrete.functor W.obj) (colimit.isColimit _) fun j => hW j.as
  have := isoLocus_obj₃ τ _ hT hsum hsum 0
  exact isIso_app_of_iso τ ((shiftFunctorZero D ℤ).app X) this

end Triangulated

end StacksDraft.CompactDevissage

end
