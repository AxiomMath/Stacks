module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GlobalSectionsSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.GUnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An étale slice through a point with separable residue field

Let `t : E ⟶ W` be a morphism of schemes locally of finite presentation and flat at a point `e`,
let `s : E ⟶ U` be a morphism to an affine scheme, and let `f₁, …, f_r ∈ Γ(U, 𝒪_U)`. Suppose the
pullbacks `s^♯ f_i` map to a regular sequence generating the maximal ideal of the local ring
`𝒪_{E_w, e}` of the fibre of `t` over `w = t(e)`, and that `κ(e)/κ(w)` is finite separable. Then
the base change `E ×_U V(f₁, …, f_r)` of the zero scheme of the `f_i` contains an open
subscheme through `e` which is étale over `W`.

## Main results

* `Stacks.AlgebraicGeometry.maximalIdeal_le_map_sup_ofList_of_fiber`: if germs at `x` generate
  the maximal ideal of the fibre, they generate the maximal ideal of `𝒪_{X, x}` together with
  the maximal ideal of the base.
* `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_fiber_generators`: criterion (7) of Stacks 02GF
  for a slice `Z ⟶ X ⟶ S` whose equations generate the maximal ideal of the fibre.
* `Stacks.AlgebraicGeometry.exists_isOpenImmersion_etale_pullback_zeroScheme`: if the slice
  `E ×_U V(f₁, …, f_r)` is unramified over `W` at a point over `e`, some open subscheme of it
  through that point is étale over `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

/-- Transport of a stalk element along an equality of points is the canonical isomorphism of
stalks attached to that equality. -/
theorem stalkCongr_hom_eq_rec {X : Scheme.{u}} {a b : X} (h : a = b)
    (y : X.presheaf.stalk a) :
    (X.presheaf.stalkCongr (.of_eq h)).hom y = h ▸ y := by
  subst h
  simp

/-- An element of `𝒪_{X, x}` lies in the maximal ideal iff its image in the local ring of the
fibre does. -/
private theorem fiber_map_mem_maximalIdeal_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (b : X.presheaf.stalk x) :
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ b) ∈
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
    b ∈ maximalIdeal (X.presheaf.stalk x) := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  rw [isUnit_map_iff, ← stalkCongr_hom_eq_rec]
  exact (MulEquiv.isUnit_map (X.presheaf.stalkCongr
    (.of_eq (f.fiberι_asFiber x).symm)).commRingCatIsoToRingEquiv.toMulEquiv)

/-- An element of `𝒪_{X, x}` whose image in the local ring of the fibre is a non-unit is a
non-unit. -/
theorem mem_maximalIdeal_of_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (b : X.presheaf.stalk x)
    (hb : ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ b) ∈
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    b ∈ maximalIdeal (X.presheaf.stalk x) :=
  (fiber_map_mem_maximalIdeal_iff f x b).1 hb

/-- **Generators of the maximal ideal of a fibre.** If the images in the local ring
`𝒪_{X_y, x}` of the fibre of finitely many elements of `𝒪_{X, x}` generate its maximal ideal,
then those elements generate the maximal ideal of `𝒪_{X, x}` together with the image of the
maximal ideal of `𝒪_{Y, y}`. -/
theorem maximalIdeal_le_map_sup_ofList_of_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    {r : ℕ} (a : Fin r → X.presheaf.stalk x)
    (h : Ideal.ofList (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ a i)) =
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    maximalIdeal (X.presheaf.stalk x) ≤
      Ideal.map (f.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (f x))) ⊔
        Ideal.ofList (List.ofFn a) := by
  intro y hy
  set I := Ideal.map (f.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (f x)))
  set e := quotientStalkEquivFiberStalk f x
  have hψ : ∀ b, ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ b) =
      e (Ideal.Quotient.mk I b) := by
    intro b
    rw [quotientStalkEquivFiberStalk_mk, stalkCongr_hom_eq_rec]
  have hy' : e (Ideal.Quotient.mk I y) ∈
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
    rw [← hψ, fiber_map_mem_maximalIdeal_iff]
    exact hy
  rw [← h] at hy'
  have hlist : (List.ofFn fun i : Fin r =>
      ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ a i)) =
      (List.ofFn fun i => Ideal.Quotient.mk I (a i)).map e.toRingHom := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hψ (a i)
  rw [hlist, ← Ideal.map_ofList, RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, RingEquiv.symm_apply_apply] at hy'
  have hy'' : Ideal.Quotient.mk I y ∈
      Ideal.map (Ideal.Quotient.mk I) (Ideal.ofList (List.ofFn a)) := by
    rwa [Ideal.map_ofList, List.map_ofFn]
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hy''
  rwa [sup_comm]

/-- A finite separable extension stays finite separable when the top field is replaced by an
isomorphic one. -/
theorem finite_isSeparable_comp_of_bijective {K L M : Type*} [Field K] [Field L] [Field M]
    (a : K →+* L) (b : L →+* M) (hb : Function.Bijective b)
    (h : letI := a.toAlgebra; Module.Finite K L ∧ Algebra.IsSeparable K L) :
    letI := (b.comp a).toAlgebra; Module.Finite K M ∧ Algebra.IsSeparable K M := by
  let := a.toAlgebra
  let := (b.comp a).toAlgebra
  obtain ⟨hfin, hsep⟩ := h
  let σ : L ≃ₐ[K] M := AlgEquiv.ofBijective
    { toRingHom := b, commutes' := fun _ => rfl } hb
  exact ⟨Module.Finite.equiv σ.toLinearEquiv, Algebra.IsSeparable.of_algHom _ _ σ.symm.toAlgHom⟩

/-- **Unramifiedness of a slice at a point with separable residue field (Stacks 02GF, (7)).**
Let `ψ : Z ⟶ X` be surjective on stalks and kill global functions `F₁, …, F_r` of `X`, and let
`k : X ⟶ S`. If the germs of the `F_i` at `ψ z` generate the maximal ideal of the local ring of the
fibre of `k` there, and `κ(ψ z)/κ(k(ψ z))` is finite separable, then `ψ ≫ k` is unramified at
`z`. -/
@[sga "3 XI 1.3" "(ii)"]
theorem unramifiedAt_comp_of_fiber_generators {Z X S : Scheme.{u}} (ψ : Z ⟶ X)
    [SurjectiveOnStalks ψ] (k : X ⟶ S) [LocallyOfFiniteType (ψ ≫ k)] {r : ℕ}
    (F : Fin r → Γ(X, ⊤)) (hvan : ∀ i, ψ.appTop (F i) = 0) (z : Z)
    (hmax : Ideal.ofList (List.ofFn fun i : Fin r =>
        ((k.fiberι (k (ψ z))).stalkMap (k.asFiber (ψ z))).hom
          ((k.fiberι_asFiber (ψ z)).symm ▸ X.presheaf.germ ⊤ (ψ z) trivial (F i))) =
      maximalIdeal ((k.fiber (k (ψ z))).presheaf.stalk (k.asFiber (ψ z))))
    (hsep : letI := (k.residueFieldMap (ψ z)).hom.toAlgebra
      Module.Finite (S.residueField (k (ψ z))) (X.residueField (ψ z)) ∧
        Algebra.IsSeparable (S.residueField (k (ψ z))) (X.residueField (ψ z))) :
    UnramifiedAt (ψ ≫ k) z := by
  have hψsurj : Function.Surjective (ψ.stalkMap z).hom := ψ.stalkMap_surjective z
  have hstalk : (ψ ≫ k).stalkMap z = k.stalkMap (ψ z) ≫ ψ.stalkMap z :=
    Scheme.Hom.stalkMap_comp ψ k z
  have hA : Ideal.map ((ψ ≫ k).stalkMap z).hom (maximalIdeal (S.presheaf.stalk ((ψ ≫ k) z))) =
      maximalIdeal (Z.presheaf.stalk z) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]
    · rw [← map_maximalIdeal_of_surjective _ hψsurj, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap]
      have hb' := maximalIdeal_le_map_sup_ofList_of_fiber k (ψ z)
        (fun i => X.presheaf.germ ⊤ (ψ z) trivial (F i)) hmax hb
      have hle : Ideal.map (ψ.stalkMap z).hom
          (Ideal.map (k.stalkMap (ψ z)).hom (maximalIdeal (S.presheaf.stalk (k (ψ z)))) ⊔
            Ideal.ofList (List.ofFn fun i => X.presheaf.germ ⊤ (ψ z) trivial (F i))) ≤
          Ideal.map ((ψ ≫ k).stalkMap z).hom (maximalIdeal (S.presheaf.stalk ((ψ ≫ k) z))) := by
        rw [Ideal.map_sup, Ideal.map_map, ← CommRingCat.hom_comp, ← hstalk]
        refine sup_le le_rfl ?_
        rw [Ideal.map_ofList, Ideal.ofList, Ideal.span_le]
        intro y hy
        simp only [Set.mem_setOf_eq, List.map_ofFn, List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        have h0 : (ψ.stalkMap z).hom
            (X.presheaf.germ ⊤ (ψ z) trivial (F i)) = 0 :=
          (Scheme.Hom.germ_stalkMap_apply ψ ⊤ z trivial (F i)).trans <|
            (congrArg (fun y => (Z.presheaf.germ (ψ ⁻¹ᵁ ⊤) z trivial).hom y) (hvan i)).trans
              (map_zero _)
        rw [Function.comp_apply, h0]
        exact zero_mem _
      exact hle (Ideal.mem_map_of_mem _ hb')
  have hB : let := ((ψ ≫ k).residueFieldMap z).hom.toAlgebra
      Module.Finite (S.residueField ((ψ ≫ k) z)) (Z.residueField z) ∧
        Algebra.IsSeparable (S.residueField ((ψ ≫ k) z))
          (Z.residueField z) := by
    have hsurj : Function.Surjective (ψ.residueFieldMap z).hom := by
      intro y
      obtain ⟨c, rfl⟩ := Z.residue_surjective z y
      obtain ⟨b, rfl⟩ := hψsurj c
      exact ⟨X.residue (ψ z) b,
        by simpa using congrArg (fun φ => φ.hom b) (Scheme.residue_residueFieldMap ψ z)⟩
    rw [Scheme.residueFieldMap_comp ψ k z]
    exact finite_isSeparable_comp_of_bijective _ _ ⟨RingHom.injective _, hsurj⟩ hsep
  exact ((unramifiedAt_tfae (ψ ≫ k) z).out 7 1).1 (And.intro hA hB)

/-- If `f` is unramified at `j x` for an open immersion `j`, then `j ≫ f` is unramified at
`x`. -/
theorem unramifiedAt_comp_of_isOpenImmersion {X X' S : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ S) [LocallyOfFiniteType f] (x : X')
    (h : UnramifiedAt f (j x)) : UnramifiedAt (j ≫ f) x := by
  rw [unramifiedAt_iff_formallyUnramified_stalkMap] at h ⊢
  have he : Arrow.mk (f.stalkMap (j x)) ≅ Arrow.mk ((j ≫ f).stalkMap x) := by
    refine Arrow.isoMk' _ _ (Iso.refl _) (asIso (j.stalkMap x)) ?_
    simp [Scheme.Hom.stalkMap_comp]
  exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff he).mp h

/-- **An étale slice through a point.** Let `t : E ⟶ W` be locally of finite presentation and
flat at `e`, let `s : E ⟶ U` with `U` affine, and let `f₁, …, f_r ∈ Γ(U, 𝒪_U)` whose pullbacks
`s^♯ f_i` map to a regular sequence in the local ring of the fibre `E_{t(e)}` at `e`. If the
base change `E ×_U V(f₁, …, f_r) ⟶ E ⟶ W` is unramified at a point `e'` over `e`, then an open
subscheme of `E ×_U V(f₁, …, f_r)` through `e'` is étale over `W`. -/
theorem exists_isOpenImmersion_etale_pullback_zeroScheme
    {E U W : Scheme.{u}} [IsAffine U] (s : E ⟶ U) (t : E ⟶ W)
    [LocallyOfFinitePresentation t] (e : E) (hflat : IsFlatAt t.toLRSHom.toShHom e)
    {r : ℕ} (f : Fin r → Γ(U, ⊤))
    (hregular : RingTheory.Sequence.IsRegular ((t.fiber (t e)).presheaf.stalk (t.asFiber e))
      (List.ofFn fun i : Fin r => ((t.fiberι (t e)).stalkMap (t.asFiber e)).hom
        ((t.fiberι_asFiber e).symm ▸ E.presheaf.germ ⊤ e trivial (s.appTop (f i)))))
    (I : U.IdealSheafData) (hI : I = Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn f)))
    (e' : ↥(pullback s I.subschemeι)) (he' : pullback.fst s I.subschemeι e' = e)
    (hunr : UnramifiedAt (pullback.fst s I.subschemeι ≫ t) e') :
    ∃ (P : Scheme.{u}) (p : P ⟶ pullback s I.subschemeι),
      IsOpenImmersion p ∧ e' ∈ Set.range p ∧ Etale (p ≫ pullback.fst _ _ ≫ t) := by
  obtain ⟨D, j, hj, hD, ⟨d, rfl⟩, hfl, hfp⟩ :=
    exists_affine_openImmersion_flat_zeroScheme_of_isRegular_fiber t e
      (fun i => s.appTop (f i)) hflat hregular
  have : IsAffine D := hD
  have hJ : Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => j.appTop (s.appTop (f i)))) = I.comap (j ≫ s) := by
    rw [hI, comap_ofIdealTop, Ideal.map_ofList, List.map_ofFn]
    congr 2
  rw [hJ] at hfl hfp
  let q : (I.comap (j ≫ s)).subscheme ⟶ pullback s I.subschemeι :=
    (I.comapIso (j ≫ s)).hom ≫ (pullbackRightPullbackFstIso s I.subschemeι j).inv ≫
      pullback.snd j (pullback.fst s I.subschemeι)
  have hq : q ≫ pullback.fst s I.subschemeι = (I.comap (j ≫ s)).subschemeι ≫ j := by
    simp only [q, Category.assoc, ← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  obtain ⟨w₀, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := j)
    (g := pullback.fst s I.subschemeι) d e' he'.symm
  let z : (I.comap (j ≫ s)).subscheme :=
    (I.comapIso (j ≫ s)).inv ((pullbackRightPullbackFstIso s I.subschemeι j).hom w₀)
  have hqz : q z = e' := by
    simp only [q, z, ← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc, hw₂]
  have hun : UnramifiedAt (q ≫ pullback.fst s I.subschemeι ≫ t) z :=
    unramifiedAt_comp_of_isOpenImmersion q _ z (hqz ▸ hunr)
  rw [← Category.assoc, hq, Category.assoc] at hun
  have hEt : EtaleAt ((I.comap (j ≫ s)).subschemeι ≫ j ≫ t) z :=
    (etaleAt_iff_isFlatAt_and_gUnramifiedAt _ z).2
      ⟨Flat.stalkMap _ z, (gUnramifiedAt_iff_unramifiedAt _ z).2 hun⟩
  obtain ⟨O, -, hzO, hOet⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt _ z hEt
  refine ⟨O.toScheme, O.ι ≫ q, inferInstance, ⟨⟨z, hzO⟩, hqz⟩, ?_⟩
  rwa [Category.assoc, ← Category.assoc q, hq, Category.assoc]

end Stacks.AlgebraicGeometry

end
