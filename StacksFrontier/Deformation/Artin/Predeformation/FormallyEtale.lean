module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SpecOver
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.Deformation.Artin.Predeformation.Transport
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityLevelLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Deformations along a formally étale chart

Let `a : F ⟶ G` be a formally étale transformation of presheaves on the big fppf site of `S`
(Stacks 049S). Then `a` has unique lifts along every thickening of spectra with nilpotent kernel,
the thickening being a composite of first-order ones. In particular, for an Artinian local
`Λ`-algebra `A` with residue field `k`, `a` is a bijection from the sections of `F` over `Spec A`
restricting to a given section `x₀` over `Spec k` onto the sections of `G` restricting to `a(x₀)`.

Consequently, if `k : (Sch/W) ⟶ 𝒲` is a 1-morphism to a category fibred in groupoids represented
by a presheaf `Q`, whose representing map `W ⟶ Q` is formally étale (for instance étale,
Stacks 04AL), then `k` induces an equivalence `𝓕_{(Sch/W),k,w₀} ≃ 𝓕_{𝒲,k,r₀}` over `𝒞_Λ` for
every object `r₀` of `𝒲` vertically isomorphic to `k(w₀)`. This is the step of the proof of
Stacks 0DSB which identifies the deformation category of the diagonal point of `R = U ×_𝒳 U`
with that of a point of an étale scheme chart of the algebraic space `R`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_lift_specOverHom_of_isNilpotent`.
* `Deformation.Artin.existsUnique_lift_of_formallyEtale`: the deformation version.
* `Deformation.Artin.predeformationEquivalenceOfFormallyEtale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Unique lifts along a thickening of spectra with nilpotent kernel.** A formally étale
transformation `a : F ⟶ G` has exactly one lift in every square over the morphism
`Spec A₀ ⟶ Spec A` induced by a surjection `A ⟶ A₀` of algebras over a ring `R'` with nilpotent
kernel: the thickening is a composite of first-order thickenings of spectra of quotients
of `A`. -/
theorem existsUnique_lift_specOverHom_of_isNilpotent {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (ha : FormallyEtale a)
    {R' : Type u} [CommRing R'] (s₀ : Spec (.of R') ⟶ S) (n : ℕ) :
    ∀ {A A₀ : Type u} [CommRing A] [CommRing A₀] [Algebra R' A] [Algebra R' A₀] [Algebra A A₀]
      [IsScalarTower R' A A₀],
      Function.Surjective (algebraMap A A₀) →
      RingHom.ker (algebraMap A A₀) ^ n = ⊥ →
      ∀ (hA : B.Contains (Spec (.of A))) (hA₀ : B.Contains (Spec (.of A₀)))
        (x₀ : F.obj (op (specOver B S hS s₀ A₀ hA₀))) (y : G.obj (op (specOver B S hS s₀ A hA))),
        G.map (specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)).op y =
          a.app _ x₀ →
        ∃! x : F.obj (op (specOver B S hS s₀ A hA)),
          F.map (specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)).op x = x₀ ∧
            a.app _ x = y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A A₀ _ _ _ _ _ _ hπ hn hA hA₀ x₀ y hy
  by_cases h2 : n ≤ 2
  · have hi : IsSquareZeroClosedImmersion B S hS
        (specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀)) :=
      Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom (algebraMap A A₀)) hπ
        (eq_bot_iff.2 ((Ideal.pow_le_pow_right h2).trans hn.le))
    exact ha _ _ (inferInstanceAs (IsAffine (Spec (.of A₀))))
      (inferInstanceAs (IsAffine (Spec (.of A)))) _ hi x₀ y hy.symm
  push Not at h2
  set K := RingHom.ker (algebraMap A A₀) with hK
  let A₁ := A ⧸ K ^ (n - 1)
  let : Algebra A₁ A₀ := (Ideal.Quotient.lift (K ^ (n - 1)) (algebraMap A A₀) fun a ha =>
    (RingHom.mem_ker).1 (Ideal.pow_le_self (by omega) ha)).toAlgebra
  have : IsScalarTower A A₁ A₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R' A A₁ := inferInstance
  have : IsScalarTower R' A₁ A₀ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R' A A₁, IsScalarTower.algebraMap_apply R' A A₀,
      IsScalarTower.algebraMap_apply A A₁ A₀]
  have hA₁ : B.Contains (Spec (.of A₁)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA
      ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _))
  have hπ₁ : Function.Surjective (algebraMap A₁ A₀) := by
    intro a₀
    obtain ⟨a, rfl⟩ := hπ a₀
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker₁ : RingHom.ker (algebraMap A₁ A₀) = K.map (Ideal.Quotient.mk (K ^ (n - 1))) := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.2 (Ideal.pow_le_self (by omega)),
      RingHom.mem_ker, RingHom.mem_ker]
    rfl
  let i₁ := specOverHom B S hS s₀ hA₁ hA₀ (IsScalarTower.toAlgHom R' A₁ A₀)
  let i₂ := specOverHom B S hS s₀ hA hA₁ (IsScalarTower.toAlgHom R' A A₁)
  have hi : specOverHom B S hS s₀ hA hA₀ (IsScalarTower.toAlgHom R' A A₀) = i₁ ≫ i₂ := by
    rw [specOverHom_comp]
    rfl
  have h₁ := ih (n - 1) (by omega) (A := A₁) (A₀ := A₀) hπ₁ (by
    rw [hker₁, ← Ideal.map_pow, Ideal.map_quotient_self])
  have h₂ := ih 2 (by omega) (A := A) (A₀ := A₁) Ideal.Quotient.mk_surjective (by
      rw [show RingHom.ker (algebraMap A A₁) = K ^ (n - 1) from Ideal.mk_ker, ← pow_mul]
      exact eq_bot_iff.2 ((Ideal.pow_le_pow_right (by omega)).trans hn.le))
  rw [hi] at hy ⊢
  simp only [op_comp, Functor.map_comp_apply] at hy ⊢
  obtain ⟨x₁, ⟨hx₁, hax₁⟩, hu₁⟩ := h₁ hA₁ hA₀ x₀ (G.map i₂.op y) hy
  obtain ⟨x, ⟨hx, hax⟩, hu⟩ := h₂ hA hA₁ x₁ y hax₁.symm
  refine ⟨x, ⟨by rw [hx, hx₁], hax⟩, fun x' ⟨hx', hax'⟩ => hu x' ⟨?_, hax'⟩⟩
  refine hu₁ _ ⟨hx', ?_⟩
  rw [← hax']
  exact NatTrans.naturality_apply a i₂.op x'

end AlgebraicGeometry.Space

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of the site over `S` is determined by its image in `Over S`. -/
theorem post_obj_injective :
    Function.Injective (Over.post B.inclusion : BigFppfOver B S hS ⥤ Over S).obj := by
  intro U V h
  have hl : U.left = V.left := ObjectProperty.FullSubcategory.ext (congrArg Over.left h)
  apply CostructuredArrow.obj_ext U V hl
  apply B.inclusion.map_injective
  have hw : (eqToHom h).left ≫ ((Over.post B.inclusion).obj V).hom =
      ((Over.post B.inclusion).obj U).hom := Over.w (eqToHom h)
  rw [Over.eqToHom_left] at hw
  simpa [Over.post] using hw

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)

/-- The spectrum of an object of `𝒞_Λ` underlying an object of the site lies in the site. -/
theorem contains_spec_of_post_eq_site {A : Type u} [CommRing A] [Algebra Λ A]
    {T : BigFppfOver B S hS}
    (hT : (Over.post B.inclusion).obj T =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)) :
    B.Contains (Spec (.of A)) :=
  contains_spec_of_post_eq B S hS (𝟭 _) _ (Xf := T) hT

/-- An object of the site whose image in `Over S` is `Spec A ⟶ Spec Λ ⟶ S` equals
`Space.specOver B S hS iΛ A`. -/
theorem eq_specOver_of_post_eq {A : Type u} [CommRing A] [Algebra Λ A] {T : BigFppfOver B S hS}
    (hT : (Over.post B.inclusion).obj T =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ)) :
    T = Space.specOver B S hS iΛ A (contains_spec_of_post_eq_site iΛ hT) :=
  post_obj_injective (hT.trans rfl)

/-- **Deformations along a formally étale transformation.** Let `a : F ⟶ G` be formally étale,
let `A` be an Artinian local `Λ`-algebra with residue field `k`, and let `i : T ⟶ T'` be a
morphism of the site lying over the closed point `Spec k ⟶ Spec A`. Then every section `y` of `G`
over `T'` restricting to `a(x₀)` is `a(x)` for exactly one section `x` of `F` over `T'` restricting
to `x₀`. -/
@[sga "3 XI 1.8" "étale clause"]
theorem existsUnique_lift_of_formallyEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (ha : Space.FormallyEtale a) (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    {T T' : BigFppfOver B S hS}
    (hT : (Over.post B.inclusion).obj T =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hT' : (Over.post B.inclusion).obj T' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ))
    (i : T ⟶ T')
    (hi : eqToHom (congrArg Over.left hT).symm ≫ ((Over.post B.inclusion).map i).left ≫
      eqToHom (congrArg Over.left hT') = Spec.map (CommRingCat.ofHom (residueMap A)))
    (x₀ : F.obj (op T)) (y : G.obj (op T')) (hy : G.map i.op y = a.app _ x₀) :
    ∃! x : F.obj (op T'), F.map i.op x = x₀ ∧ a.app _ x = y := by
  have e := eq_specOver_of_post_eq iΛ hT
  have e' := eq_specOver_of_post_eq iΛ hT'
  generalize contains_spec_of_post_eq_site iΛ hT = hk at e
  generalize contains_spec_of_post_eq_site iΛ hT' = hA at e'
  subst e e'
  let : Algebra A k := (residueMap A).toAlgebra
  have : IsScalarTower Λ A k := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap Λ k r = A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A r))
    rw [← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      AlgEquiv.commutes]
  have hii : i = Space.specOverHom B S hS iΛ hA hk (IsScalarTower.toAlgHom Λ A k) := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Space.toScheme_map_specOverHom]
    show ((Over.post B.inclusion).map i).left = Spec.map (CommRingCat.ofHom (residueMap A))
    rw [← hi]
    rfl
  subst hii
  have hπ : Function.Surjective (algebraMap A k) := by
    intro c
    obtain ⟨r, hr⟩ := A.residueEquiv.surjective c
    obtain ⟨r', rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨r', by change residueMap A r' = c; simp [residueMap, hr]⟩
  have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
    ext r
    show residueMap A r = 0 ↔ _
    simp [residueMap, IsLocalRing.residue_eq_zero_iff]
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  exact Space.existsUnique_lift_specOverHom_of_isNilpotent a ha iΛ n hπ
    (by rwa [hker]) hA hk x₀ y hy

section Chart

variable (W : BigFppfOver B S hS) {𝒲 : Type v} [Category.{w} 𝒲]
  (p𝒲 : 𝒲 ⥤ BigFppfOver B S hS) (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eQ : StacksRepresentableCFG.EquivalenceOver p𝒲 (presheafOfCategories (Q ⋙ typeToCat)).p)
  (K : Over W ⥤ 𝒲) (hK : K ⋙ p𝒲 = Over.forget W) (a : yoneda.obj W ⟶ Q)

variable {W p𝒲 K} in
/-- The image under `p𝒲` of `K.map f` is `f.left`, up to the identifications `p𝒲 ∘ K = forget`. -/
theorem map_map_eq_of_comp_eq_forget {u u' : Over W} (f : u ⟶ u') : p𝒲.map (K.map f) =
    eqToHom (Functor.congr_obj hK u) ≫ f.left ≫ eqToHom (Functor.congr_obj hK u').symm := by
  simpa using Functor.congr_hom hK f

/-- If the representing map of `K` is formally étale, then a morphism `K(y) ⟶ K(x)` compatible
with two deformations `x`, `y` of `w₀` is the image of a morphism `y ⟶ x`. -/
theorem exists_map_eq_of_formallyEtale (ha : Space.FormallyEtale a)
    (hKa : ∀ u : Over W, a.app (op u.left) u.hom =
      PresheafOfCategories.sectionOfObj eQ (K.obj u) (Functor.congr_obj hK u))
    (w₀ : Over W)
    (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (x y : DeformationObject iΛ (Over.forget W ⋙ Over.post B.inclusion) w₀ hw₀)
    (β : K.obj y.point ⟶ K.obj x.point) (hβ : K.map y.arrow ≫ β = K.map x.arrow) :
    ∃ α : y.point ⟶ x.point, K.map α = β := by
  have hset : p𝒲.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eQ
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection Q)
  let f : y.point.left ⟶ x.point.left := eqToHom (Functor.congr_obj hK y.point).symm ≫
    p𝒲.map β ≫ eqToHom (Functor.congr_obj hK x.point)
  have hβf : p𝒲.IsHomLift f β :=
    IsHomLift.of_fac' p𝒲 f β (Functor.congr_obj hK y.point) (Functor.congr_obj hK x.point)
      (by simp [f])
  have hif : y.arrow.left ≫ f = x.arrow.left := by
    have h := congrArg p𝒲.map hβ
    rw [Functor.map_comp, map_map_eq_of_comp_eq_forget hK,
      map_map_eq_of_comp_eq_forget hK] at h
    simpa [f] using congrArg (fun t => eqToHom (Functor.congr_obj hK w₀).symm ≫ t ≫
      eqToHom (Functor.congr_obj hK x.point)) h
  have hy : Q.map y.arrow.left.op (a.app (op y.point.left) y.point.hom) =
      a.app (op w₀.left) w₀.hom :=
    (NatTrans.naturality_apply a y.arrow.left.op y.point.hom).symm.trans
      (congrArg (a.app (op w₀.left)) (Over.w y.arrow))
  have key : y.point.hom = f ≫ x.point.hom := by
    obtain ⟨z, _, hz⟩ := existsUnique_lift_of_formallyEtale (T := w₀.left)
      (T' := y.point.left) iΛ a ha y.algebra hw₀ y.base y.arrow.left y.arrow_base
      w₀.hom (a.app (op y.point.left) y.point.hom) hy
    have h₁ : (yoneda.obj W).map y.arrow.left.op (f ≫ x.point.hom) = w₀.hom := by
      show y.arrow.left ≫ f ≫ x.point.hom = w₀.hom
      rw [← Category.assoc, hif]
      exact Over.w x.arrow
    have h₂ : a.app (op y.point.left) (f ≫ x.point.hom) =
        a.app (op y.point.left) y.point.hom := by
      have h₃ : a.app (op y.point.left) (f ≫ x.point.hom) =
          Q.map f.op (a.app (op x.point.left) x.point.hom) :=
        NatTrans.naturality_apply a f.op x.point.hom
      rw [h₃, hKa, hKa]
      exact (PresheafOfCategories.sectionOfObj_map eQ _ _ f β hβf).symm
    exact (hz _ ⟨Over.w y.arrow, rfl⟩).trans (hz _ ⟨h₁, h₂⟩).symm
  refine ⟨Over.homMk f key.symm, ?_⟩
  have : p𝒲.IsHomLift f β := hβf
  have : p𝒲.IsHomLift f (K.map (Over.homMk f key.symm)) :=
    IsHomLift.of_fac' p𝒲 f _ (Functor.congr_obj hK y.point) (Functor.congr_obj hK x.point)
      (by rw [map_map_eq_of_comp_eq_forget hK]; rfl)
  exact StacksRepresentableCFG.pfaithful_lift hset f _ _

/-- If the representing map of `K` is formally étale, then every deformation of `r₀` is
isomorphic, compatibly with `ψ : r₀ ⟶ K(w₀)`, to the image under `K` of a deformation of `w₀`. -/
theorem exists_deformationObject_of_formallyEtale (ha : Space.FormallyEtale a)
    (hKa : ∀ u : Over W, a.app (op u.left) u.hom =
      PresheafOfCategories.sectionOfObj eQ (K.obj u) (Functor.congr_obj hK u))
    (w₀ : Over W)
    (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) (r₀ : 𝒲)
    (hr₀ : (p𝒲 ⋙ Over.post B.inclusion).obj r₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ψ : r₀ ⟶ K.obj w₀) [IsIso ψ]
    (hψ : (p𝒲 ⋙ Over.post B.inclusion).map ψ =
      eqToHom (hr₀.trans ((transport_obj_eq B hS (Over.forget W) p𝒲 K hK w₀).trans hw₀).symm))
    (c : DeformationObject iΛ (p𝒲 ⋙ Over.post B.inclusion) r₀ hr₀) :
    ∃ (d : DeformationObject iΛ (Over.forget W ⋙ Over.post B.inclusion) w₀ hw₀)
      (ψ' : c.point ⟶ K.obj d.point) (_ : d.algebra = c.algebra)
      (H : (p𝒲 ⋙ Over.post B.inclusion).obj c.point =
        (p𝒲 ⋙ Over.post B.inclusion).obj (K.obj d.point)),
      c.arrow ≫ ψ' = ψ ≫ K.map d.arrow ∧ (p𝒲 ⋙ Over.post B.inclusion).map ψ' = eqToHom H := by
  have hset : p𝒲.IsFiberedInSetoids :=
    StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eQ
      (PresheafOfCategories.isFiberedInSetoids_discreteProjection Q)
  have hwK : p𝒲.obj (K.obj w₀) = w₀.left := Functor.congr_obj hK w₀
  let i : w₀.left ⟶ p𝒲.obj c.point := eqToHom hwK.symm ≫ p𝒲.map (inv ψ ≫ c.arrow)
  have hψinv : p𝒲.map (inv ψ) = eqToHom (post_obj_injective (hr₀.trans
      ((transport_obj_eq B hS (Over.forget W) p𝒲 K hK w₀).trans hw₀).symm)).symm := by
    apply (Over.post B.inclusion).map_injective
    rw [eqToHom_map, Functor.map_inv, Functor.map_inv]
    show inv ((p𝒲 ⋙ Over.post B.inclusion).map ψ) = _
    simp only [hψ, inv_eqToHom]
  have hi : eqToHom (congrArg Over.left hw₀).symm ≫ ((Over.post B.inclusion).map i).left ≫
      eqToHom (congrArg Over.left c.base) =
        Spec.map (CommRingCat.ofHom (residueMap c.algebra)) := by
    rw [← c.arrow_base]
    simp only [i, Functor.map_comp, hψinv, eqToHom_map, Over.comp_left, Over.eqToHom_left,
      Category.assoc, eqToHom_trans_assoc]
    rfl
  have hiL : p𝒲.IsHomLift i (inv ψ ≫ c.arrow) :=
    IsHomLift.of_fac' p𝒲 i _ hwK rfl (by simp [i])
  obtain ⟨x, ⟨hx, hax⟩, -⟩ := existsUnique_lift_of_formallyEtale iΛ a ha c.algebra hw₀ c.base
    i hi w₀.hom (PresheafOfCategories.sectionOfObj eQ c.point rfl)
    ((PresheafOfCategories.sectionOfObj_map eQ rfl _ i _ hiL).symm.trans (hKa w₀).symm)
  let d : DeformationObject iΛ (Over.forget W ⋙ Over.post B.inclusion) w₀ hw₀ :=
    { algebra := c.algebra
      point := Over.mk x
      arrow := Over.homMk i hx
      base := c.base
      arrow_base := hi }
  have hs : PresheafOfCategories.sectionOfObj eQ c.point rfl =
      PresheafOfCategories.sectionOfObj eQ (K.obj d.point) (Functor.congr_obj hK d.point) := by
    rw [← hKa]
    exact hax.symm
  let e := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eQ rfl
    (Functor.congr_obj hK d.point) hs
  let ψ' : c.point ⟶ K.obj d.point := e.hom.1
  have hψ'L : p𝒲.IsHomLift (𝟙 (p𝒲.obj c.point)) ψ' := e.hom.2
  have hψ'map : p𝒲.map ψ' = eqToHom (Functor.congr_obj hK d.point).symm := by
    rw [IsHomLift.fac' p𝒲 (𝟙 (p𝒲.obj c.point)) ψ']
    simp
  refine ⟨d, ψ', rfl, congrArg (Over.post B.inclusion).obj
    (Functor.congr_obj hK d.point).symm, ?_, ?_⟩
  · apply StacksRepresentableCFG.pfaithful hset
    rw [Functor.map_comp, Functor.map_comp, hψ'map, map_map_eq_of_comp_eq_forget hK]
    show p𝒲.map c.arrow ≫ _ = p𝒲.map ψ ≫ _ ≫ (eqToHom hwK.symm ≫
      p𝒲.map (inv ψ ≫ c.arrow)) ≫ _
    rw [Functor.map_comp, Functor.map_inv]
    simp
  · show (Over.post B.inclusion).map (p𝒲.map ψ') = _
    rw [hψ'map, eqToHom_map]

/-- **Stacks 0DSB, the étale chart step.** Let `𝒲` be a category fibred in groupoids over the big
fppf site represented by a presheaf `Q`, let `K : (Sch/W) ⟶ 𝒲` be a 1-morphism whose
representing map `a : W ⟶ Q` is formally étale, let `w₀` be a point of `W` over `Spec k` and let
`ψ : r₀ ⟶ K(w₀)` be a vertical isomorphism. Then `K` induces an equivalence
`𝓕_{(Sch/W),k,w₀} ≃ 𝓕_{𝒲,k,r₀}` over `𝒞_Λ`.

The representing map is recorded by `hKa`: it sends the section `u` of `W` to the section of `Q`
named by `K(u)`. -/
noncomputable def predeformationEquivalenceOfFormallyEtale
    (h𝒲 : p𝒲.IsFiberedInGroupoids) (ha : Space.FormallyEtale a)
    (hKa : ∀ u : Over W, a.app (op u.left) u.hom =
      PresheafOfCategories.sectionOfObj eQ (K.obj u) (Functor.congr_obj hK u))
    (w₀ : Over W)
    (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) (r₀ : 𝒲)
    (hr₀ : (p𝒲 ⋙ Over.post B.inclusion).obj r₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ψ : r₀ ⟶ K.obj w₀) [IsIso ψ]
    (hψ : (p𝒲 ⋙ Over.post B.inclusion).map ψ =
      eqToHom (hr₀.trans ((transport_obj_eq B hS (Over.forget W) p𝒲 K hK w₀).trans hw₀).symm)) :
    letI := (predeformationCategory iΛ (Over.forget W ⋙ Over.post B.inclusion) w₀ hw₀).category
    letI := (predeformationCategory iΛ (p𝒲 ⋙ Over.post B.inclusion) r₀ hr₀).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iΛ (Over.forget W ⋙ Over.post B.inclusion) w₀ hw₀).projection
      (predeformationCategory iΛ (p𝒲 ⋙ Over.post B.inclusion) r₀ hr₀).projection := by
  haveI : K.Faithful := Functor.Faithful.of_comp_eq hK
  exact transportPredeformationEquivalence B hS iΛ (Over.forget W) p𝒲 K hK w₀ hw₀ r₀ hr₀ ψ
    (Functor.IsFiberedInGroupoids.over_forget W) h𝒲 hψ
    (fun x y β hβ => exists_map_eq_of_formallyEtale iΛ W p𝒲 Q eQ K hK a ha hKa w₀ hw₀ x y β hβ)
    (exists_deformationObject_of_formallyEtale iΛ W p𝒲 Q eQ K hK a ha hKa w₀ hw₀ r₀ hr₀ ψ hψ)

end Chart

end Deformation.Artin

end
