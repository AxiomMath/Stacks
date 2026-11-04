module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.DirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.RingTheory.PushoutTrace

/-!
# Linear forms on `k'` and the direct image of `𝐆_a` from a scalar extension

Let `X` be a scheme over a field `k`, let `k'/k` be a field extension and let
`g : X_{k'} ⟶ X` be the scalar extension. For an affine étale `X`-scheme `U` the global functions
on `U ×_X X_{k'} = U ×_k k'` are `Γ(U) ⊗_k k'`. A `k`-linear form `ℓ : k' → k` therefore gives the
trace `id ⊗ ℓ : Γ(U ×_X X_{k'}) ⟶ Γ(U)` on affine objects, natural in `U`, and hence a morphism
of sheaves `g_* 𝐆_{a, X_{k'}} ⟶ 𝐆_{a, X}`. Composed with the pullback of functions and with
multiplication by `c ∈ k'` it is multiplication by `ℓ(c)`. On cohomology this shows that a
`k'`-linear relation among restrictions of classes gives `k`-linear relations after every
linear form, which is the injectivity half of the flat base change of [Stacks, Tag 02KH] for
`H^q(X, 𝒪_X)` along `k ⟶ k'`, read on the étale side.

## Main definitions

* `Stacks.ArtinSchreier.scalarExtensionTrace`: the trace `g_* 𝐆_{a, X_{k'}} ⟶ 𝐆_{a, X}` of `ℓ`.

## Main results

* `Stacks.ArtinSchreier.additiveDirectImageComparison_comp_smul_comp_scalarExtensionTrace`: the
  trace undoes multiplication by `c ∈ k'` up to the scalar `ℓ(c)`.
* `Stacks.ArtinSchreier.sum_smul_eq_zero_of_sum_smul_restriction_eq_zero`: the consequence on
  cohomology.

## Implementation notes

The ring-level trace is `CommRingCat.pushoutTrace` for the pushout square of global sections of
`U ×_k Spec k'` (`AlgebraicGeometry.isPushout_appTop_of_isPullback`), and the sheaf morphism is
obtained from the dense subsite of affine étale schemes by
`CategoryTheory.Functor.IsCoverDense.sheafHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- The spectrum map of the field extension. -/
abbrev specExt : Spec (.of k') ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- **`U ×_X X_{k'} = U ×_k k'`**: the base change of an étale `X`-scheme along the scalar
extension is its scalar extension. -/
theorem isPullback_scalarExtension_baseChange (V : X.Etale) :
    IsPullback (pullback.snd V.hom (scalarExtensionFst k k' f) ≫
        pullback.snd f (specExt k k'))
      (pullback.fst V.hom (scalarExtensionFst k k' f)) (specExt k k') (V.hom ≫ f) :=
  (IsPullback.of_hasPullback V.hom (scalarExtensionFst k k' f)).flip.paste_horiz
    (IsPullback.of_hasPullback f (specExt k k')).flip

/-- The ring-level pushout square `Γ(U ×_X X_{k'}) = Γ(U) ⊗_k k'` for `U` affine. -/
theorem isPushout_scalarExtension_baseChange (V : X.Etale) (hV : IsAffine V.left) :
    IsPushout (specExt k k').appTop (V.hom ≫ f).appTop
      (pullback.snd V.hom (scalarExtensionFst k k' f) ≫ pullback.snd f (specExt k k')).appTop
      (pullback.fst V.hom (scalarExtensionFst k k' f)).appTop :=
  have : IsAffine ((𝟭 Scheme).obj V.left) := hV
  isPushout_appTop_of_isPullback (isPullback_scalarExtension_baseChange k k' f V)

variable {k k'} (ℓ : k' →ₗ[k] k) {q : ℕ}

/-- A `k`-linear form on `k'`, transported to the rings of global functions of the two spectra. -/
def specLinearForm : Γ(Spec (.of k'), ⊤) →+ Γ(Spec (.of k), ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv.hom.toAddMonoidHom.comp ℓ.toAddMonoidHom).comp
    (Scheme.ΓSpecIso (.of k')).hom.hom.toAddMonoidHom

/-- `specLinearForm ℓ` sends the global function `c` on `Spec k'` to the global function `ℓ c`
on `Spec k`. -/
theorem specLinearForm_ΓSpecIso_inv (c : k') :
    specLinearForm ℓ ((Scheme.ΓSpecIso (.of k')).inv c) = (Scheme.ΓSpecIso (.of k)).inv (ℓ c) := by
  show (Scheme.ΓSpecIso (.of k)).inv (ℓ ((Scheme.ΓSpecIso (.of k')).hom
    ((Scheme.ΓSpecIso (.of k')).inv c))) = _
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of k')).inv, Iso.inv_hom_id]
  rfl

/-- `specLinearForm ℓ` is linear over `Γ(Spec k, ⊤)`, acting on `Γ(Spec k', ⊤)` through
`specExt k k'`. -/
theorem specLinearForm_mul (r : Γ(Spec (.of k), ⊤)) (y : Γ(Spec (.of k'), ⊤)) :
    specLinearForm ℓ ((specExt k k').appTop r * y) = r * specLinearForm ℓ y := by
  have h := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (algebraMap k k')))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  show (Scheme.ΓSpecIso (.of k)).inv (ℓ ((Scheme.ΓSpecIso (.of k')).hom
      ((specExt k k').appTop r * y))) =
    r * (Scheme.ΓSpecIso (.of k)).inv (ℓ ((Scheme.ΓSpecIso (.of k')).hom y))
  rw [map_mul, h, ← Algebra.smul_def, ℓ.map_smul, smul_eq_mul, map_mul]
  congr 1
  exact (CommRingCat.comp_apply _ _ r).symm.trans (by rw [Iso.hom_inv_id]; rfl)

/-- The underlying scheme of an affine étale `X`-scheme is affine. -/
theorem isAffine_affineEtale (R : X.AffineEtale) :
    IsAffine ((Scheme.AffineEtale.Spec X).obj R).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- **The trace `Γ(U ×_k k') → Γ(U)` of a linear form `ℓ : k' → k`** on the affine étale
`X`-schemes, as a morphism of presheaves on the affine étale site. -/
def scalarExtensionTraceAffine :
    (Scheme.AffineEtale.Spec X).op ⋙
        ((etaleAbelianDirectImage.{u, 0} (scalarExtensionFst k k' f)).obj
          (additiveSheaf.{u, u + 1} (scalarExtension k k' f))).obj ⟶
      (Scheme.AffineEtale.Spec X).op ⋙ (additiveSheaf.{u, u + 1} X).obj where
  app R := AddCommGrpCat.ofHom
    ((AddEquiv.ulift.symm.toAddMonoidHom.comp
      (CommRingCat.pushoutTrace (isPushout_scalarExtension_baseChange k k' f
        ((Scheme.AffineEtale.Spec X).obj R.unop) (isAffine_affineEtale R.unop))
        (specLinearForm ℓ) (specLinearForm_mul ℓ))).comp AddEquiv.ulift.toAddMonoidHom)
  naturality R₁ R₂ h := by
    ext ⟨x⟩
    let G := Scheme.AffineEtale.Spec X
    let V₁ := G.obj R₁.unop
    let V₂ := G.obj R₂.unop
    let e := G.map h.unop
    change ofSection.{u, u + 1} (CommRingCat.pushoutTrace (isPushout_scalarExtension_baseChange
        k k' f V₂ (isAffine_affineEtale R₂.unop)) (specLinearForm ℓ) (specLinearForm_mul ℓ)
          (((smallEtaleBaseChange (scalarExtensionFst k k' f)).map e).left.appTop x)) =
      ofSection.{u, u + 1} (e.left.appTop (CommRingCat.pushoutTrace
        (isPushout_scalarExtension_baseChange k k' f V₁ (isAffine_affineEtale R₁.unop))
          (specLinearForm ℓ) (specLinearForm_mul ℓ) x))
    congr 1
    have hw : e.left ≫ V₁.hom = V₂.hom := MorphismProperty.Over.w e
    refine CommRingCat.pushoutTrace_naturality _ _ _ _ e.left.appTop
      ((smallEtaleBaseChange (scalarExtensionFst k k' f)).map e).left.appTop ?_ ?_ ?_ x
    · exact (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hw)))
    · exact (Scheme.Hom.comp_appTop _ _).symm.trans ((congrArg Scheme.Hom.appTop
        (pullback.lift_fst _ _ _)).trans (Scheme.Hom.comp_appTop _ _))
    · exact (Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))))

/-- **The trace `g_* 𝐆_{a, X_{k'}} ⟶ 𝐆_{a, X}` of a `k`-linear form `ℓ : k' → k`**, where
`g : X_{k'} ⟶ X` is the scalar extension: on an affine étale `X`-scheme `U` it is
`id ⊗ ℓ : Γ(U) ⊗_k k' ⟶ Γ(U)`, and it is extended to all étale `X`-schemes from the dense subsite
of affine ones. -/
def scalarExtensionTrace :
    (etaleAbelianDirectImage.{u, 0} (scalarExtensionFst k k' f)).obj
        (additiveSheaf.{u, u + 1} (scalarExtension k k' f)) ⟶ additiveSheaf.{u, u + 1} X :=
  ⟨Functor.IsCoverDense.sheafHom (G := Scheme.AffineEtale.Spec X)
    (scalarExtensionTraceAffine f ℓ)⟩

/-- The structure morphism of the scalar extension. -/
abbrev scalarExtensionSnd : scalarExtension k k' f ⟶ Spec (.of k') :=
  pullback.snd f (specExt k k')

/-- The pullback of `baseScalarSection K h c` along `e : Z ⟶ Y` is the image of `c` in `Γ(Z, ⊤)`
along `e ≫ h`. -/
theorem appTop_baseScalarSection {Y : Scheme.{u}} (K : Type u) [Field K] (h : Y ⟶ Spec (.of K))
    {Z : Scheme.{u}} (e : Z ⟶ Y) (c : K) :
    e.appTop (baseScalarSection K h c) = (e ≫ h).appTop ((Scheme.ΓSpecIso (.of K)).inv c) := by
  rw [baseScalarSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.appLE_top_top]
  rfl

/-- **The trace undoes multiplication by `c ∈ k'` up to the scalar `ℓ c ∈ k`.** Pulling a function
back to `X_{k'}`, multiplying by `c` and applying the trace of `ℓ` is multiplication by `ℓ c`. -/
theorem additiveDirectImageComparison_comp_smul_comp_scalarExtensionTrace (c : k') :
    additiveDirectImageComparison (scalarExtensionFst k k' f) ≫
        (etaleAbelianDirectImage.{u, 0} (scalarExtensionFst k k' f)).map
          (additiveSheafSmul (scalarExtension k k' f)
            (baseScalarSection k' (scalarExtensionSnd (k' := k') f) c)) ≫
        scalarExtensionTrace f ℓ =
      additiveSheafSmul X (baseScalarSection k f (ℓ c)) := by
  let G := Scheme.AffineEtale.Spec X
  apply Sheaf.hom_ext
  refine (Functor.IsCoverDense.sheafHom_eq G _).symm.trans
    (Eq.trans ?_ (Functor.IsCoverDense.sheafHom_eq G _))
  congr 1
  ext R x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (X := X) (U := G.obj R.unop) x
  have hτ := congrArg (fun t => t.app R) (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := G) (scalarExtensionTraceAffine f ℓ))
  let V := G.obj R.unop
  let hpo := isPushout_scalarExtension_baseChange k k' f V (isAffine_affineEtale R.unop)
  have h1 := ConcreteCategory.congr_hom hτ (ofSection.{u, u + 1}
    (U := (smallEtaleBaseChange (scalarExtensionFst k k' f)).obj V)
      ((pullback.fst V.hom (scalarExtensionFst k k' f)).appTop x *
        (pullback.snd V.hom (scalarExtensionFst k k' f)).appTop
          (baseScalarSection k' (scalarExtensionSnd (k' := k') f) c)))
  refine h1.trans ?_
  show ofSection.{u, u + 1} (CommRingCat.pushoutTrace hpo (specLinearForm ℓ)
      (specLinearForm_mul ℓ) ((pullback.fst V.hom (scalarExtensionFst k k' f)).appTop x *
        (pullback.snd V.hom (scalarExtensionFst k k' f)).appTop
          (baseScalarSection k' (scalarExtensionSnd (k' := k') f) c))) =
    ofSection.{u, u + 1} (x * pullTop V (baseScalarSection k f (ℓ c)))
  rw [appTop_baseScalarSection, pullTop, appTop_baseScalarSection,
    CommRingCat.pushoutTrace_α_mul_β, specLinearForm_ΓSpecIso_inv]

section Cohomology

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **Linear independence over `k` survives restriction to `X_{k'}`, in the form needed for the
base change of cohomology.** If `∑ cᵢ · ρ(vᵢ) = 0` in `H^q(X_{k'}, 𝐆_a)`, where `ρ` is restriction
along `X_{k'} ⟶ X` and `cᵢ ∈ k'` act by multiplication, then `∑ ℓ(cᵢ) · vᵢ = 0` in
`H^q(X, 𝐆_a)` for every `k`-linear form `ℓ : k' → k`. -/
theorem sum_smul_eq_zero_of_sum_smul_restriction_eq_zero {ι : Type*} (s : Finset ι)
    (c : ι → k') (v : ι → Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) q)
    (h : ∑ i ∈ s, Sheaf.H.map (additiveSheafSmul (scalarExtension k k' f)
        (baseScalarSection k' (scalarExtensionSnd (k' := k') f) (c i))) q
          (additiveRestriction (scalarExtensionFst k k' f) q (v i)) = 0) :
    ∑ i ∈ s, Sheaf.H.map (additiveSheafSmul X (baseScalarSection k f (ℓ (c i)))) q (v i) = 0 := by
  let g := scalarExtensionFst k k' f
  have : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback f (specExt k k')).flip (inferInstance : IsAffineHom (specExt k k'))
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} g
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let e := (etaleAbelianInverseImageConstantIso.{u, 0} g).app (AddCommGrpCat.of (ULift ℤ))
  let F : Ext.{w} Z ((etaleAbelianDirectImage.{u, 0} g).obj
      (additiveSheaf.{u, u + 1} (scalarExtension k k' f))) q →+
        Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} (scalarExtension k k' f)) q :=
    ((Ext.mk₀ e.inv).precomp _ (zero_add q)).comp (Stacks.ExtAdjunction.extMap adj Z _ q)
  have hF : Function.Injective F :=
    ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e.inv q).comp
      (extMap_bijective_additiveSheaf.{w} g Z q)).injective
  let m := fun i => additiveSheafSmul (scalarExtension k k' f)
    (baseScalarSection k' (scalarExtensionSnd (k' := k') f) (c i))
  have key : ∀ i, Sheaf.H.map (m i) q (additiveRestriction g q (v i)) =
      F (Sheaf.H.map (additiveDirectImageComparison g ≫
        (etaleAbelianDirectImage.{u, 0} g).map (m i)) q (v i)) := by
    intro i
    rw [additiveRestriction_eq_extMap, Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero,
      ← Stacks.ExtAdjunction.extMap_naturality_mk₀, Sheaf.H.map_comp_apply]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => key i), ← map_sum] at h
  have h0 := hF (h.trans (map_zero F).symm)
  have h1 := congrArg (Sheaf.H.map (scalarExtensionTrace f ℓ) q) h0
  rw [map_sum, map_zero] at h1
  refine Eq.trans ?_ h1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Sheaf.H.map_comp_apply, Category.assoc,
    additiveDirectImageComparison_comp_smul_comp_scalarExtensionTrace]

end Cohomology

end Stacks.ArtinSchreier

end
