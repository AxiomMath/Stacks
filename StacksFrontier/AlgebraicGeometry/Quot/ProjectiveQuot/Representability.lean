module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.HilbertLocus
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationRecovery
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernelIso
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistEquivalence

/-!
# `Quot^P` is represented by the Hilbert locus `Z_P`

Let `m = regularityIndex n r hr P`, `N = freeRank n r m`, `p = quotRank n r hr P` with `p ≤ N`, and
`Z_P ⟶ G = G(N - p, N)` the Hilbert locus of the flat locus of the universal family `ℱ_G`
(`AlgebraicGeometry.ProjectiveQuot.hilbertLocusHom`). This file proves that `Z_P` represents
`T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)`:

* for `K ∈ Quot^P(T)`, the pullback of `ℱ_G` along the classifying morphism `toGrassmannian K` is
  `𝒬(m)` under `𝒪^{⊕ r}(m)` (the cokernel of `u_m` for the presentation of `K` is `𝒬(m)`), so it is
  flat with fibrewise Hilbert functions `P(· + m)`, and `toGrassmannian K` factors through `Z_P`;
* conversely, for `t : T ⟶ G` factoring through `Z_P`, `ℱ_t = (ℙⁿ_t)^* ℱ_G` is flat with Hilbert
  functions `P(· + m)`; untwisting, `𝒪^{⊕ r} ⟶ ℱ_t(-m)` is onto, and its kernel `K_t` lies in
  `Quot^P(T)`, with `toGrassmannian K_t = t` (the Grassmannian point is recovered from
  `ℱ_t`, `AlgebraicGeometry.ProjectiveQuot.eq_toGrassmannian_of_iso`);
* the two constructions are inverse, and `K ↦ toGrassmannian K` is natural in `T`.

This is the representability of `Quot^P` by a scheme in the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.hilbertFunctorIso`:
  `hilbertFunctor n r P ≅ yoneda.obj Z_P ⋙ uliftFunctor`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Generic facts in an abelian category -/

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- A subobject is the kernel of its cokernel map. -/
theorem kernelSubobject_cokernel_π_arrow {X : C} (S : Subobject X) :
    kernelSubobject (cokernel.π S.arrow) = S := by
  refine le_antisymm ?_ (le_kernelSubobject _ _ (cokernel.condition _))
  exact Subobject.le_of_comm (Abelian.monoLift S.arrow (kernelSubobject (cokernel.π S.arrow)).arrow
    (kernelSubobject_arrow_comp _)) (Abelian.monoLift_comp _ _ _)

/-- **Two subobjects with isomorphic quotients under `X` are equal.** -/
theorem eq_of_cokernel_iso {X : C} (K K' : Subobject X) (e : cokernel K.arrow ≅ cokernel K'.arrow)
    (h : cokernel.π K.arrow ≫ e.hom = cokernel.π K'.arrow) : K = K' := by
  rw [← kernelSubobject_cokernel_π_arrow K, ← kernelSubobject_cokernel_π_arrow K', ← h,
    kernelSubobject_comp_mono]

end CategoryTheory.Abelian

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ} (hr : 1 ≤ r) {P : Polynomial ℚ}

/-- Bookkeeping in an arbitrary category: `(b⁻¹ ≫ a) ≫ e = c` from `a ≫ e = b ≫ c`. -/
theorem inv_comp_comp_eq_of_eq {C : Type*} [Category* C] {W X Y Z : C} (b : X ≅ W) (a : X ⟶ Y)
    (e : Y ⟶ Z) (c : W ⟶ Z) (h : a ≫ e = b.hom ≫ c) : (b.inv ≫ a) ≫ e = c := by
  rw [Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Bookkeeping in an arbitrary category: `a ≫ e₁ ≫ e₂ = b ≫ c` from `a ≫ e₁ = b ≫ d` and
`d ≫ e₂ = c`. -/
theorem comp_comp_eq_of_eq {C : Type*} [Category* C] {W X Y Z V : C} (a : W ⟶ X) (e₁ : X ⟶ Y)
    (e₂ : Y ⟶ Z) (b : W ⟶ V) (d : V ⟶ Y) (c : V ⟶ Z) (h₁ : a ≫ e₁ = b ≫ d) (h₂ : d ≫ e₂ = c) :
    a ≫ e₁ ≫ e₂ = b ≫ c := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- The quotient map `𝒪^{⊕ r}(m) ⟶ ℱ_t = (ℙⁿ_t)^* ℱ_G` for `t : T ⟶ G`. -/
def familyπ {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    twist (regularityIndex.{u} n r hr P : ℤ) (freeModule n r T) ⟶
      (Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj (universalFamily.{u} n r hr P) :=
  (freeTwistPullbackIso n r t _).inv ≫
    (Scheme.Modules.pullback (projectiveSpaceOverMap n t)).map (presentationCokernelπ _ _)

/-- The quotient map `𝒪^{⊕ r}(m) ⟶ ℱ_t` is an epimorphism. -/
instance {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) : Epi (familyπ hr t) := by
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback (projectiveSpaceOverMap n t)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverMap n t)).leftAdjoint_preservesColimits
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) _
    (@Functor.map_epi _ _ _ _ (Scheme.Modules.pullback (projectiveSpaceOverMap n t)) inferInstance
      _ _ (presentationCokernelπ _ _) inferInstance)

/-- **`ℱ_{toGrassmannian K} ≅ 𝒬(m)`** under `𝒪^{⊕ r}(m)`, for `K ∈ Quot^P(T)`. -/
theorem exists_family_iso_twist_quotient
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    ∃ e : (Scheme.Modules.pullback (projectiveSpaceOverMap n (toGrassmannian hr hp hK))).obj
        (universalFamily.{u} n r hr P) ≅ twist (regularityIndex.{u} n r hr P : ℤ) (quotient K),
      familyπ hr (toGrassmannian hr hp hK) ≫ e.hom =
        twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K) := by
  obtain ⟨e₁, he₁⟩ := exists_pullback_universalFamily_iso hr hp hK
  obtain ⟨e₂, he₂⟩ := exists_presentationCokernel_iso_twist_quotient hr hp hK
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  have h : (Scheme.Modules.pullback (projectiveSpaceOverMap n (toGrassmannian hr hp hK))).map
      (presentationCokernelπ _ _) ≫ e₁.hom ≫ e₂.hom =
        (freeTwistPullbackIso n r (toGrassmannian hr hp hK) _).hom ≫
          twistMap (regularityIndex.{u} n r hr P : ℤ) (quotientπ K) :=
    comp_comp_eq_of_eq _ _ _ _ _ _ he₁ he₂
  exact inv_comp_comp_eq_of_eq _ _ _ _ h

/-- Bookkeeping in an arbitrary category: `c ≫ e⁻¹ = b⁻¹ ≫ a` from `a ≫ e = b ≫ c`. -/
theorem comp_inv_eq_inv_comp_of_eq {C : Type*} [Category* C] {W X Y Z : C} (a : X ⟶ Y)
    (e : Y ≅ Z) (b : X ≅ W) (c : W ⟶ Z) (h : a ≫ e.hom = b.hom ≫ c) :
    c ≫ e.inv = b.inv ≫ a := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Bookkeeping for a functor `F`: `a ≫ b ≫ y ≫ F c' = F q` from `a ≫ b = x`, `x ≫ y = F ρ`
and `ρ ≫ c' = q`. -/
theorem comp_comp_comp_map_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {B X' : D} {U V W : C} (a : F.obj U ⟶ B) (b : B ⟶ X') (x : F.obj U ⟶ X')
    (y : X' ⟶ F.obj V)
    (ρ : U ⟶ V) (c' : V ⟶ W) (q : U ⟶ W) (h₁ : a ≫ b = x) (h₂ : x ≫ y = F.map ρ)
    (h₃ : ρ ≫ c' = q) : a ≫ b ≫ y ≫ F.map c' = F.map q := by
  rw [← Category.assoc a, h₁, ← Category.assoc, h₂, ← F.map_comp, h₃]

/-- **`toGrassmannian K` factors through `Z_P`.** -/
theorem exists_lift_toGrassmannian
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    ∃ w : T ⟶ (hilbertLocus.{u} n r hr P).toScheme,
      w ≫ hilbertLocusHom.{u} n r hr P = toGrassmannian hr hp hK := by
  obtain ⟨e, -⟩ := exists_family_iso_twist_quotient hr hp hK
  have := hK.1.1
  refine (exists_lift_hilbertLocusHom_iff _).2 ⟨(isFlatOver_iff_of_iso _ e).2
    (isFlatOver_twist _ _ _ hK.1.2), fun t' d => ?_⟩
  rw [fibreHilbert_eq_of_iso e t', fibreHilbert_twist]
  exact_mod_cast (hasFibreHilbertPolynomial_iff (quotient K)).1 hK.2 t'
    (d + (regularityIndex.{u} n r hr P : ℤ))

/-- **The morphism `T ⟶ Z_P` classifying `K ∈ Quot^P(T)`.** -/
def toHilbertLocus
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    T ⟶ (hilbertLocus.{u} n r hr P).toScheme :=
  (exists_lift_toGrassmannian hr hp hK).choose

/-- The composite of `toHilbertLocus K` with `Z_P ⟶ G` is `toGrassmannian K`. -/
theorem toHilbertLocus_comp
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    toHilbertLocus hr hp hK ≫ hilbertLocusHom.{u} n r hr P = toGrassmannian hr hp hK :=
  (exists_lift_toGrassmannian hr hp hK).choose_spec

/-- The untwisting `ℱ_t(m)(-m) ≅ ℱ_t`. -/
abbrev familyUntwistIso {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :=
  twistTwistNegIso T (regularityIndex.{u} n r hr P : ℤ)
    ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj (universalFamily.{u} n r hr P))

/-- The untwisted quotient map `ρ_t : 𝒪^{⊕ r} ⟶ ℱ_t(-m)`, whose twist by `m` is `ℱ_t`'s quotient
map. -/
def familyQuotientMap {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    freeModule n r T ⟶ twist (-(regularityIndex.{u} n r hr P : ℤ))
      ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj (universalFamily.{u} n r hr P)) :=
  (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).preimage
    (familyπ hr t ≫ (familyUntwistIso hr t).inv)

/-- The twist by `m` of `ρ_t` is the quotient map `𝒪^{⊕ r}(m) ⟶ ℱ_t` followed by the inverse of the
untwisting `ℱ_t(m)(-m) ≅ ℱ_t`. -/
theorem twistFunctor_map_familyQuotientMap {T : Scheme.{u}}
    (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).map (familyQuotientMap hr t) =
      familyπ hr t ≫ (familyUntwistIso hr t).inv :=
  Functor.map_preimage _ _

/-- The untwisted quotient map `ρ_t : 𝒪^{⊕ r} ⟶ ℱ_t(-m)` is an epimorphism. -/
instance {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    Epi (familyQuotientMap hr t) := by
  refine epi_of_epi_twistMap (regularityIndex.{u} n r hr P : ℤ) _ ?_
  rw [twistFunctor_map_familyQuotientMap]
  infer_instance

/-- **The kernel `K_t ⊆ 𝒪^{⊕ r}`** read off `t : T ⟶ G`: the kernel of `𝒪^{⊕ r} ⟶ ℱ_t(-m)`. -/
def ofFamily {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    Subobject (freeModule n r T) :=
  kernelSubobject (familyQuotientMap hr t)

/-- The quotient `𝒪^{⊕ r}/K_t` is isomorphic to `ℱ_t(-m)` under `𝒪^{⊕ r}`. -/
theorem exists_quotient_ofFamily_iso {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P) :
    ∃ c : quotient (ofFamily hr t) ≅ twist (-(regularityIndex.{u} n r hr P : ℤ))
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj (universalFamily.{u} n r hr P)),
      quotientπ (ofFamily hr t) ≫ c.hom = familyQuotientMap hr t :=
  ⟨Abelian.cokernelKernelSubobjectIso (familyQuotientMap hr t),
    ((Iso.comp_inv_eq _).1 (Abelian.cokernelKernelSubobjectIso_inv_comp _)).symm⟩

/-- **`K_t ∈ Quot^P(T)` for `t` factoring through `Z_P`.** -/
theorem ofFamily_mem {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P)
    (ht : ∃ w : T ⟶ (hilbertLocus.{u} n r hr P).toScheme, w ≫ hilbertLocusHom.{u} n r hr P = t) :
    ofFamily hr t ∈ hilbertFamilies n r P T := by
  obtain ⟨hflat, hhil⟩ := (exists_lift_hilbertLocusHom_iff t).1 ht
  obtain ⟨c, -⟩ := exists_quotient_ofFamily_iso hr t
  have : (quotient (ofFamily hr t)).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso c.symm inferInstance
  refine ⟨⟨inferInstance, (isFlatOver_iff_of_iso _ c).2 (isFlatOver_twist _ _ _ hflat)⟩,
    (hasFibreHilbertPolynomial_iff _).2 fun t' d => ?_⟩
  rw [fibreHilbert_eq_of_iso c t', fibreHilbert_twist]
  have h := hhil t' (d + -(regularityIndex.{u} n r hr P : ℤ))
  push_cast at h
  rw [h]
  congr 1
  ring

/-- Any iso from `A` to `ℱ_t` compatible with a map `a` out of `𝒪^{⊕ r}(m)` and `familyπ` yields an
iso `A ≅ (𝒪^{⊕ r}/K_t)(m)` compatible with `a` and the twisted projection. -/
private theorem exists_iso_twist_quotient_ofFamily {T : Scheme.{u}}
    (t : T ⟶ quotGrassmannian.{u} n r hr P) {A : (projectiveSpaceOver n T).Modules}
    (a : twist (regularityIndex.{u} n r hr P : ℤ) (freeModule n r T) ⟶ A)
    (e : A ≅ (Scheme.Modules.pullback (projectiveSpaceOverMap n t)).obj
      (universalFamily.{u} n r hr P)) (h : a ≫ e.hom = familyπ hr t) :
    ∃ γ : A ≅ (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).obj
        (quotient (ofFamily hr t)),
      a ≫ γ.hom = (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).map
        (quotientπ (ofFamily hr t)) := by
  obtain ⟨c, hc⟩ := exists_quotient_ofFamily_iso hr t
  refine ⟨e ≪≫ (familyUntwistIso hr t).symm ≪≫
      (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).mapIso c.symm, ?_⟩
  exact comp_comp_comp_map_eq (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)) _ _ _ _ _ _ _
    h (twistFunctor_map_familyQuotientMap hr t).symm ((Iso.comp_inv_eq _).2 hc.symm)

/-- **The Grassmannian point of `K_t` is `t`.** -/
theorem toGrassmannian_ofFamily
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} (t : T ⟶ quotGrassmannian.{u} n r hr P)
    (ht : ∃ w : T ⟶ (hilbertLocus.{u} n r hr P).toScheme, w ≫ hilbertLocusHom.{u} n r hr P = t) :
    toGrassmannian hr hp (ofFamily_mem hr t ht) = t := by
  obtain ⟨e₁, he₁⟩ := exists_pullback_presentationCokernel_iso (regularityIndex.{u} n r hr P) t
    (Grassmannian.universalPresentation _ _)
  obtain ⟨γ, hγ⟩ := exists_iso_twist_quotient_ofFamily hr t _ e₁.symm
    (comp_inv_eq_inv_comp_of_eq _ _ _ _ he₁)
  exact (eq_toGrassmannian_of_iso hr hp (ofFamily_mem hr t ht) t γ
    (hγ.trans (twistMap_eq_twistFunctor_map _ _).symm)).symm

/-- **`K_{toGrassmannian K} = K`.** -/
theorem ofFamily_toGrassmannian
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    ofFamily hr (toGrassmannian hr hp hK) = K := by
  obtain ⟨e, he⟩ := exists_family_iso_twist_quotient hr (hp := hp) hK
  obtain ⟨γ, hγ⟩ := exists_iso_twist_quotient_ofFamily hr (toGrassmannian hr hp hK)
    ((twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).map (quotientπ K)) e.symm
    (by rw [Iso.symm_hom, ← twistMap_eq_twistFunctor_map, ← he, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  have hγ' : quotientπ K ≫ (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).preimage γ.hom =
      quotientπ (ofFamily hr (toGrassmannian hr hp hK)) := by
    apply (twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).map_injective
    rwa [Functor.map_comp, Functor.map_preimage]
  exact (Abelian.eq_of_cokernel_iso (C := (projectiveSpaceOver n T).Modules) K _
    ((twistFunctor n T (regularityIndex.{u} n r hr P : ℤ)).preimageIso γ) hγ').symm

/-- **`Quot^P(T) ≃ Hom(T, Z_P)`.** -/
def hilbertLocusEquiv
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P))
    (T : Scheme.{u}) :
    hilbertFamilies n r P T ≃ (T ⟶ (hilbertLocus.{u} n r hr P).toScheme) where
  toFun K := toHilbertLocus hr hp K.2
  invFun w := ⟨ofFamily hr (w ≫ hilbertLocusHom.{u} n r hr P), ofFamily_mem hr _ ⟨w, rfl⟩⟩
  left_inv K := Subtype.ext (by
    change ofFamily hr (toHilbertLocus hr hp K.2 ≫ hilbertLocusHom.{u} n r hr P) = K.1
    rw [toHilbertLocus_comp]
    exact ofFamily_toGrassmannian hr hp K.2)
  right_inv w := (cancel_mono (hilbertLocusHom.{u} n r hr P)).1 (by
    rw [toHilbertLocus_comp]
    exact toGrassmannian_ofFamily hr hp _ ⟨w, rfl⟩)

/-- **`Z_P` represents `Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}`**:
`hilbertFunctor n r P ≅ yoneda.obj Z_P ⋙ uliftFunctor`. -/
def hilbertFunctorIso
    (hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P)) :
    hilbertFunctor.{u} n r P ≅
      yoneda.obj (hilbertLocus.{u} n r hr P).toScheme ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents
    (fun T => Equiv.toIso ((hilbertLocusEquiv hr hp T.unop).trans Equiv.ulift.symm))
    (fun {T T'} g => by
      ext K
      refine ULift.ext _ _ ((cancel_mono (hilbertLocusHom.{u} n r hr P)).1 ?_)
      change toHilbertLocus hr hp (baseChange_mem_hilbertFamilies g.unop K.2) ≫ _ =
        (g.unop ≫ toHilbertLocus hr hp K.2) ≫ _
      rw [toHilbertLocus_comp, Category.assoc, toHilbertLocus_comp, comp_toGrassmannian])

end AlgebraicGeometry.ProjectiveQuot

end
