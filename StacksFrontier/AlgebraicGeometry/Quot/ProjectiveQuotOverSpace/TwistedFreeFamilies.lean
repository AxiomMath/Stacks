/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Hilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistPullbackComp
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChangeComp

/-!
# Quotients of a twisted free module on `ℙⁿ`, read as quotients of `𝒪^{⊕ r}`

Let `W` be a scheme and `𝒢` a module on `ℙⁿ_W` with an identification
`c : 𝒢 ≅ 𝒪(-d)^{⊕ r}`.  For a morphism `a : T ⟶ W` the inverse image of `𝒢` on `ℙⁿ_T` is
`𝒪(-d)^{⊕ r}` again, and twisting by `d` identifies the submodules of `a^* 𝒢` with the submodules
of `𝒪^{⊕ r}` on `ℙⁿ_T`.  This is the step of the proof of Stacks 0DPB which, after the surjection
`𝒪(-d)^{⊕ r} ⟶ ℱ` of Stacks 01Q3, reads the quotients of `𝒪(-d)^{⊕ r}` as points of the scheme
of Stacks 0DPA (Stacks 0DP7).

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.pullbackCompIso`: `(g ≫ a'')^* 𝒢 ≅ g^* a''^* 𝒢`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistedFreeIso`: `a^* 𝒢 ≅ 𝒪(-d)^{⊕ r}` on `ℙⁿ_T`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistedFreeSubobjectEquiv`: the submodules of
  `a^* 𝒢` correspond to the submodules of `𝒪^{⊕ r}` on `ℙⁿ_T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.mem_hilbertFamilies_twistedFreeSubobjectEquiv_iff`:
  a quotient of `a^* 𝒢` is a flat family with fibrewise Hilbert polynomial `P` exactly when the
  corresponding quotient of `𝒪^{⊕ r}` is one with fibrewise Hilbert polynomial `t ↦ P(t + d)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistedFreeSubobjectEquiv_subobjectPullback`: the
  correspondence commutes with base change along `T ⟶ T''` over `W`.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

/-! ### Subobjects transported along isomorphisms -/

section Transport

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- The subobjects of isomorphic objects correspond. -/
def subobjectIsoEquiv {X Y : 𝒜} (e : X ≅ Y) : Subobject X ≃ Subobject Y :=
  (Subobject.mapIsoToOrderIso e).toEquiv

omit [Abelian 𝒜] in
/-- The subobject corresponding to `K` under `subobjectIsoEquiv e` is the image of `K` under
`e.hom`. -/
theorem subobjectIsoEquiv_apply {X Y : 𝒜} (e : X ≅ Y) (K : Subobject X) :
    subobjectIsoEquiv e K = (Subobject.map e.hom).obj K :=
  rfl

/-- The transport of a kernel subobject along an isomorphism is the kernel subobject of the
transported map. -/
theorem subobjectIsoEquiv_kernelSubobject {X X' Y : 𝒜} (e : X ≅ X') (f : X ⟶ Y) :
    subobjectIsoEquiv e (kernelSubobject f) = kernelSubobject (e.inv ≫ f) := by
  show (Subobject.map e.hom).obj (Subobject.mk (kernel.ι f)) =
    Subobject.mk (kernel.ι (e.inv ≫ f))
  rw [Subobject.map_mk]
  refine (Subobject.mk_eq_mk_of_comm _ _ (kernelIsIsoComp e.inv f) ?_).symm
  simp [kernelIsIsoComp]

/-- The quotient by a transported subobject is the quotient by the subobject. -/
theorem nonempty_cokernel_subobjectIsoEquiv_iso {X X' : 𝒜} (e : X ≅ X') (K : Subobject X) :
    Nonempty (cokernel (subobjectIsoEquiv e K).arrow ≅ cokernel K.arrow) := by
  rw [show subobjectIsoEquiv e K = kernelSubobject (e.inv ≫ cokernel.π K.arrow) by
    rw [← subobjectIsoEquiv_kernelSubobject, kernelSubobject_cokernel_π]]
  exact ⟨Abelian.cokernelKernelSubobjectIso _⟩

/-- Equal morphisms have equal kernel subobjects. -/
theorem kernelSubobject_congr {X Y : 𝒜} {f f' : X ⟶ Y} (h : f = f') :
    kernelSubobject f = kernelSubobject f' :=
  h ▸ rfl

end Transport

variable {n r d : ℕ} {W : Scheme.{u}} {G : (projectiveSpaceOver n W).Modules}
  (c : G ≅ twist (-(d : ℤ)) (freeModule n r W))

/-! ### The identifications -/

/-- **`(g ≫ a'')^* 𝒢 ≅ g^* a''^* 𝒢` on projective spaces**, for `g ≫ a'' = a`: the inverse of the
composition law of pullback of modules. -/
def pullbackCompIso {T T'' W : Scheme.{u}} (g : T ⟶ T'') (a'' : T'' ⟶ W) {a : T ⟶ W}
    (h : g ≫ a'' = a) (G : (projectiveSpaceOver n W).Modules) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n a)).obj G ≅
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n a'')).obj G) :=
  (asIso (pullbackCompCongrApp (projectiveSpaceOverMap n g) (projectiveSpaceOverMap n a'')
    ((projectiveSpaceOverMap_comp n g a'').trans (congrArg (projectiveSpaceOverMap n) h)) G)).symm

/-- **The inverse image of `𝒢 ≅ 𝒪(-d)^{⊕ r}` along `ℙⁿ_T ⟶ ℙⁿ_W` is `𝒪(-d)^{⊕ r}`.** -/
def twistedFreeIso {T : Scheme.{u}} (a : T ⟶ W) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n a)).obj G ≅
      twist (-(d : ℤ)) (freeModule n r T) :=
  (Scheme.Modules.pullback (projectiveSpaceOverMap n a)).mapIso c ≪≫
    (twistPullbackIso a (-(d : ℤ)) (freeModule n r W)).symm ≪≫
    (twistFunctor n T (-(d : ℤ))).mapIso (freeModulePullbackIso n r a)

/-- **The submodules of `a^* 𝒢` and of `𝒪^{⊕ r}` on `ℙⁿ_T` correspond**: transport along
`a^* 𝒢 ≅ 𝒪(-d)^{⊕ r}`, then untwist by `d`. -/
def twistedFreeSubobjectEquiv {T : Scheme.{u}} (a : T ⟶ W) :
    Subobject ((Scheme.Modules.pullback (projectiveSpaceOverMap n a)).obj G) ≃
      Subobject (freeModule n r T) :=
  (subobjectIsoEquiv (twistedFreeIso c a)).trans
    (twistSubobjectEquiv (-(d : ℤ)) (freeModule n r T)).symm

/-- Twisting the subobject `twistedFreeSubobjectEquiv c a K` of `𝒪^{⊕ r}` by `-d` gives the
transport of `K` along `twistedFreeIso c a`. -/
theorem twistSubobjectEquiv_twistedFreeSubobjectEquiv {T : Scheme.{u}} (a : T ⟶ W)
    (K : Subobject ((Scheme.Modules.pullback (projectiveSpaceOverMap n a)).obj G)) :
    twistSubobjectEquiv (-(d : ℤ)) (freeModule n r T) (twistedFreeSubobjectEquiv c a K) =
      subobjectIsoEquiv (twistedFreeIso c a) K :=
  Equiv.apply_symm_apply _ _

/-! ### Membership -/

/-- Shifting a polynomial by `m` and then by `-m` recovers the polynomial. -/
theorem shiftPolynomial_shiftPolynomial_neg (P : Polynomial ℚ) (m : ℤ) :
    shiftPolynomial (shiftPolynomial P m) (-m) = P := by
  simp only [shiftPolynomial, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, Int.cast_neg, Polynomial.C_neg]
  rw [show Polynomial.X + -Polynomial.C (m : ℚ) + Polynomial.C (m : ℚ) = Polynomial.X by ring,
    Polynomial.comp_X]

/-- **Quotients of `a^* 𝒢` are read as quotients of `𝒪^{⊕ r}`**: a quotient of `a^* 𝒢` is a flat
family with fibrewise Hilbert polynomial `P` exactly when the corresponding quotient of
`𝒪^{⊕ r}` is a flat family with fibrewise Hilbert polynomial `t ↦ P(t + d)`. -/
theorem mem_hilbertFamilies_twistedFreeSubobjectEquiv_iff {T : Scheme.{u}} (a : T ⟶ W)
    (P : Polynomial ℚ)
    (K : Subobject ((Scheme.Modules.pullback (projectiveSpaceOverMap n a)).obj G)) :
    (IsFlatFamily (cokernel K.arrow) ∧ HasFibreHilbertPolynomial P (cokernel K.arrow)) ↔
      twistedFreeSubobjectEquiv c a K ∈ hilbertFamilies n r (shiftPolynomial P d) T := by
  set K₀ := twistedFreeSubobjectEquiv c a K
  obtain ⟨e₁⟩ := nonempty_cokernel_subobjectIsoEquiv_iso (twistedFreeIso c a) K
  have e₂ : cokernel (subobjectIsoEquiv (twistedFreeIso c a) K).arrow ≅
      twist (-(d : ℤ)) (quotient K₀) := by
    rw [← twistSubobjectEquiv_twistedFreeSubobjectEquiv]
    exact twistSubobjectCokernelIso _ _ _
  let e : cokernel K.arrow ≅ twist (-(d : ℤ)) (quotient K₀) := e₁.symm ≪≫ e₂
  rw [mem_hilbertFamilies_iff]
  have hP := hasFibreHilbertPolynomial_twist_iff (shiftPolynomial P d) (-(d : ℤ)) (quotient K₀)
  rw [shiftPolynomial_shiftPolynomial_neg] at hP
  constructor
  · rintro ⟨hf, hh⟩
    have hf' : IsFlatFamily (quotient K₀) :=
      (isFlatFamily_twist_iff (-(d : ℤ)) _).1 (isFlatFamily_of_iso e hf)
    exact ⟨hf', (hP hf'.1).1 (hasFibreHilbertPolynomial_of_iso hf.1 e hh)⟩
  · rintro ⟨hf, hh⟩
    have hf' : IsFlatFamily (twist (-(d : ℤ)) (quotient K₀)) := isFlatFamily_twist _ hf
    exact ⟨isFlatFamily_of_iso e.symm hf',
      hasFibreHilbertPolynomial_of_iso hf'.1 e.symm ((hP hf.1).2 hh)⟩

/-! ### Naturality -/

/-- The composite `a^* 𝒢 ≅ g^* a''^* 𝒢 ≅ g^* 𝒪(-d)^{⊕ r}` is
`a^* 𝒢 ≅ 𝒪(-d)^{⊕ r} ≅ g^* 𝒪(-d)^{⊕ r}`. -/
theorem pullbackCompIso_hom_twistedFreeIso {T T'' : Scheme.{u}} (g : T ⟶ T'') (a'' : T'' ⟶ W)
    {a : T ⟶ W} (h : g ≫ a'' = a) :
    (pullbackCompIso g a'' h G).hom ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistedFreeIso c a'').hom =
      (twistedFreeIso c a).hom ≫
        (twistFunctor n T (-(d : ℤ))).map (freeModulePullbackIso n r g).inv ≫
        (twistPullbackIso g (-(d : ℤ)) (freeModule n r T'')).hom := by
  subst h
  set w := (projectiveSpaceOverMap_comp n g a'').trans
    (congrArg (projectiveSpaceOverMap n) (rfl : g ≫ a'' = g ≫ a''))
  set Ψ := pullbackCompCongrApp (projectiveSpaceOverMap n g) (projectiveSpaceOverMap n a'') w
  have hΨ : ∀ {A B} (φ : A ⟶ B), Ψ A ≫ (Scheme.Modules.pullback
      (projectiveSpaceOverMap n (g ≫ a''))).map φ =
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        ((Scheme.Modules.pullback (projectiveSpaceOverMap n a'')).map φ) ≫ Ψ B := by
    intro A B φ
    have n₁ := (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
      (projectiveSpaceOverMap n a'')).hom.naturality φ
    have n₂ := (Scheme.Modules.pullbackCongr w).hom.naturality φ
    simp only [Functor.comp_map] at n₁
    simp only [Ψ, pullbackCompCongrApp, Category.assoc, n₂, reassoc_of% n₁]
  have hcomp := twistPullbackIso_hom_comp_of_eq g a'' (rfl : g ≫ a'' = g ≫ a'') (-(d : ℤ))
    (freeModule n r W)
  have hnat := twistPullbackIso_hom_naturality g (-(d : ℤ)) (freeModulePullbackIso n r a'').hom
  rw [twistMap_eq_twistFunctor_map, twistMap_eq_twistFunctor_map] at hnat
  rw [twistMap_eq_twistFunctor_map] at hcomp
  have hc := hΨ c.hom
  simp only [Ψ, pullbackCompCongrApp, Category.assoc] at hc
  have hfree' : (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
      (freeModulePullbackIso n r a'').hom =
      (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
          (projectiveSpaceOverMap n a'')).hom.app (freeModule n r W) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (freeModule n r W) ≫
        (freeModulePullbackIso n r (g ≫ a'')).hom ≫ (freeModulePullbackIso n r g).inv := by
    have hfree2 : (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
          (freeModulePullbackIso n r a'').inv ≫
        (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
          (projectiveSpaceOverMap n a'')).hom.app (freeModule n r W) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (freeModule n r W) =
        (freeModulePullbackIso n r g).hom ≫ (freeModulePullbackIso n r (g ≫ a'')).inv := by
      rw [← freeModulePullbackIso_inv_comp (n := n) (r := r) g a'']
      simp
    rw [← cancel_epi ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
      (freeModulePullbackIso n r a'').inv), reassoc_of% hfree2]
    simp [← Functor.map_comp]
  rw [pullbackCompIso, Iso.symm_hom, Iso.inv_comp_eq, asIso_hom]
  simp only [twistedFreeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc, pullbackCompCongrApp]
  rw [reassoc_of% hc]
  congr 1
  rw [← cancel_epi ((twistPullbackIso g (-(d : ℤ))
      ((Scheme.Modules.pullback (projectiveSpaceOverMap n a'')).obj (freeModule n r W))).hom ≫
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (twistPullbackIso a'' (-(d : ℤ)) (freeModule n r W)).hom)]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [← hnat, reassoc_of% hcomp.symm, Iso.hom_inv_id_assoc, hfree']
  simp only [Functor.map_comp, Category.assoc]

/-- **The correspondence commutes with base change**: for `g : T ⟶ T''` over `W`, the
submodule of `𝒪^{⊕ r}` on `ℙⁿ_T` corresponding to the base change of `K ⊆ a''^* 𝒢` along
`ℙⁿ_T ⟶ ℙⁿ_{T''}` is the base change of the submodule corresponding to `K`. -/
theorem twistedFreeSubobjectEquiv_subobjectPullback {T T'' : Scheme.{u}} (g : T ⟶ T'')
    (a'' : T'' ⟶ W) {a : T ⟶ W} (h : g ≫ a'' = a)
    (K : Subobject ((Scheme.Modules.pullback (projectiveSpaceOverMap n a'')).obj G)) :
    twistedFreeSubobjectEquiv c a (subobjectPullback g (pullbackCompIso g a'' h G) K) =
      baseChange g (twistedFreeSubobjectEquiv c a'' K) := by
  apply (twistSubobjectEquiv (-(d : ℤ)) (freeModule n r T)).injective
  rw [twistSubobjectEquiv_twistedFreeSubobjectEquiv]
  have hbc : baseChange g (twistedFreeSubobjectEquiv c a'' K) =
      subobjectPullback g (freeModulePullbackIso n r g).symm
        (twistedFreeSubobjectEquiv c a'' K) := rfl
  rw [hbc, twistSubobjectEquiv_subobjectPullback, twistSubobjectEquiv_twistedFreeSubobjectEquiv,
    ← kernelSubobject_cokernel_π K, subobjectPullback_kernelSubobject,
    subobjectIsoEquiv_kernelSubobject, subobjectIsoEquiv_kernelSubobject,
    subobjectPullback_kernelSubobject]
  refine kernelSubobject_congr ?_
  have key' : (pullbackCompIso g a'' h G).hom = (twistedFreeIso c a).hom ≫
      ((twistFunctor n T (-(d : ℤ))).map (freeModulePullbackIso n r g).inv ≫
        (twistPullbackIso g (-(d : ℤ)) (freeModule n r T'')).hom) ≫
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistedFreeIso c a'').inv := by
    rw [← Category.assoc, ← pullbackCompIso_hom_twistedFreeIso c g a'' h, Category.assoc,
      Iso.map_hom_inv_id, Category.comp_id]
  rw [key']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
