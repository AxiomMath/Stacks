module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalDictionary
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartAdic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Ring maps over an affine open of the base

In the last part of the proof of Stacks 0GI5 the base is replaced by an affine open
`O = Spec R ⊆ S`, every object lies over `O`, and "all of the ring maps above are `R`-algebra
homomorphisms as all of the morphisms are morphisms over `S`". This file supplies the three
translations used there.

* `AlgebraicGeometry.Artin.exists_stage_range_subset_of_isLimit`: if `V = lim V_k` (cofiltered,
  affine stages) lies over an open `O ⊆ S`, so does every stage below some stage (Stacks 01Z3).
* `AlgebraicGeometry.Artin.exists_comp_ι_eq_of_range_subset`: such a stage then maps to `O`.
* `AlgebraicGeometry.Artin.FormalDictionary.continuousHomOfComp`: a continuous ring map
  `φ : B → A^∧` which is `R`-linear is a continuous map over `S`, when the stages of `B` lie over
  `O` through `R → B` and `V = Spec A` lies over `O`.
* `AlgebraicGeometry.Artin.FormalDictionary.toRingHom_comp_eq_of_isOver`: conversely, a
  continuous map over `S` is `R`-linear.

Here the structure of `B` over `O` is a ring map `ρ : R → B` such that each quotient stage
`Spec (B ⧸ J) ⟶ S` is `Spec (B ⧸ J) ⟶ Spec R ≅ O ⟶ S`, and `V` lies over `O` through a morphism
`f : V ⟶ O` with `f ≫ O.ι` the structure morphism of `V`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 01Z3](https://stacks.math.columbia.edu/tag/01Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A limit lying over an open lies over it at a stage** (Stacks 01Z3). Let `V = lim V_k` be a
cofiltered limit of affine locally Noetherian objects over `S`. If `V ⟶ S` maps into an open
`O ⊆ S`, then so does `V_k ⟶ S` for every `k` below some stage below any given `k₀`: otherwise
the closed sets `(V_k ⟶ S)⁻¹(S ∖ O)` are nonempty and compact, so their limit is nonempty. -/
theorem exists_stage_range_subset_of_isLimit {J : Type u} [Category.{u} J] [IsCofiltered J]
    {D : J ⥤ LocallyNoetherianOver B S hS} {κ : Cone D}
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj j)))
    (O : S.Opens) (hO : Set.range (B.inclusion.map κ.pt.obj.hom).base ⊆ (O : Set S)) (k₀ : J) :
    ∃ (k : J) (_ : k ⟶ k₀), Set.range (B.inclusion.map (D.obj k).obj.hom).base ⊆ (O : Set S) := by
  classical
  let F := D ⋙ LocallyNoetherianOver.toScheme B S hS
  have hw : ∀ {X Y : LocallyNoetherianOver B S hS} (g : X ⟶ Y),
      (LocallyNoetherianOver.toScheme B S hS).map g ≫ B.inclusion.map Y.obj.hom =
        B.inclusion.map X.obj.hom := fun {X Y} g => by
    change B.inclusion.map g.hom.left ≫ _ = _
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w g.hom)
  have hwκ : ∀ i : J, ((LocallyNoetherianOver.toScheme B S hS).mapCone κ).π.app i ≫
      B.inclusion.map (D.obj i).obj.hom = B.inclusion.map κ.pt.obj.hom := fun i => hw (κ.π.app i)
  have : ∀ j, IsAffine (F.obj j) := hD
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (F.map f) := fun _ => inferInstance
  by_contra! H
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' F
    ((LocallyNoetherianOver.toScheme B S hS).mapCone κ) hκ (j := k₀)
    (fun k _ => (B.inclusion.map (D.obj k).obj.hom).base ⁻¹' (O : Set S)ᶜ)
    (fun k _ => O.2.isClosed_compl.preimage (B.inclusion.map (D.obj k).obj.hom).continuous)
    (fun k f => by
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.mp (H k f)
      exact ⟨y, hy⟩)
    (fun k _ => by
      have : CompactSpace (F.obj k) := inferInstance
      exact IsClosed.isCompact (X := F.obj k)
        (O.2.isClosed_compl.preimage (B.inclusion.map (D.obj k).obj.hom).continuous))
    (fun k k' f _ x hx => by
      simp only [Set.mem_preimage] at hx ⊢
      rwa [← hw (D.map f), Scheme.Hom.comp_apply] at hx)
  have h := hs k₀ (𝟙 k₀)
  simp only [Set.mem_preimage, Set.mem_compl_iff] at h
  rw [← Scheme.Hom.comp_apply, hwκ] at h
  exact h (hO ⟨s, rfl⟩)

/-- A morphism `X ⟶ S` mapping into an open `O ⊆ S` factors through `O`. Used with
`exists_stage_range_subset_of_isLimit` to put a stage `V_k ⟶ S` over `O = Spec R`. -/
theorem exists_comp_ι_eq_of_range_subset {X : Scheme.{u}} (p : X ⟶ S) (O : S.Opens)
    (hO : Set.range p.base ⊆ (O : Set S)) : ∃ f : X ⟶ (O : Scheme.{u}), f ≫ O.ι = p :=
  ⟨IsOpenImmersion.lift O.ι p (by rwa [Scheme.Opens.range_ι]),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- If `f : X ⟶ O` over an affine open `O`, then `Spec Q ⟶ Spec Γ(X) ≅ X ⟶ S` is
`Spec Q ⟶ Spec Γ(O) ≅ O ⟶ S` along `Γ(O) → Γ(X) → Q`. -/
private theorem spec_map_comp_isoSpec_inv_comp_eq {X : Scheme.{u}} [IsAffine X]
    {O : S.Opens} [IsAffine (O : Scheme.{u})] {p : X ⟶ S} (f : X ⟶ (O : Scheme.{u}))
    (hf : f ≫ O.ι = p) {Q : Type u} [CommRing Q] (ψ : Γ(X, ⊤) →+* Q) :
    Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv ≫ p =
      Spec.map (CommRingCat.ofHom (ψ.comp f.appTop.hom)) ≫ (O : Scheme.{u}).isoSpec.inv ≫ O.ι := by
  rw [← hf, ← Scheme.isoSpec_inv_naturality_assoc f, ← Spec.map_comp_assoc]
  rfl

namespace FormalDictionary

attribute [local instance] Space.pointTopology

/-- The `I`-adic topology on the completion `A^∧`. -/
local instance instTopologicalSpaceAdicCompletionOverS {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable (O : S.Opens) [IsAffine (O : Scheme.{u})]
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] {DB : FormalSpace.QuotientSystem B S hS Bt}
  (ρ : Γ((O : Scheme.{u}), ⊤) →+* Bt)
  (hρ : ∀ J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J },
    DB.overS J = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J.1).comp ρ)) ≫
      (O : Scheme.{u}).isoSpec.inv ≫ O.ι)
  {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  (f : (BigFppfOver.toScheme B S hS).obj V ⟶ (O : Scheme.{u})) (hf : f ≫ O.ι = V.hom.hom)

include hρ hf in
/-- The two composites `Spec (A^∧ ⧸ K) ⟶ S` agree when `φ` is `R`-linear: both are
`Spec (A^∧ ⧸ K) ⟶ Spec R ≅ O ⟶ S` for the same ring map `R → A^∧ ⧸ K`. -/
theorem overS_of_comp_eq (φ : Bt →+* AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (hφ : φ.comp ρ =
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).comp f.appTop.hom)
    (J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J })
    (K : { K : Ideal (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) //
      TopologicalRing.IsWeakIdealOfDefinition K })
    (h : J.1 ≤ Ideal.comap φ K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ h)) ≫ DB.overS J =
      (completionQuotientSystem V I).overS K := by
  show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp
    (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom
  rw [hρ J, spec_map_comp_isoSpec_inv_comp_eq f hf, ← Spec.map_comp_assoc]
  congr 2
  ext r
  show Ideal.quotientMap K.1 φ h (Ideal.Quotient.mk J.1 (ρ r)) =
    Ideal.Quotient.mk K.1 (algebraMap _ _ (f.appTop.hom r))
  rw [Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk K.1) (RingHom.congr_fun hφ r)

/-- **A continuous `R`-linear ring map `B → A^∧` is a continuous map over `S`**, when the stages
of `B` lie over `O` through `ρ : R → B` and `V` lies over `O` through `f` (the over-`S` input of
the last step of the proof of Stacks 0GI5). -/
def continuousHomOfComp
    (φ : Bt →+* AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (hφc : Continuous φ)
    (hφ : φ.comp ρ =
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).comp
        f.appTop.hom) :
    FormalSpace.ContinuousHom DB (completionQuotientSystem V I) where
  toRingHom := φ
  continuous := hφc
  overS J K h := overS_of_comp_eq O ρ hρ I f hf φ hφ J K h

/-- The ring map underlying `continuousHomOfComp` is `φ`. -/
@[simp]
theorem continuousHomOfComp_toRingHom
    (φ : Bt →+* AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (hφc : Continuous φ)
    (hφ : φ.comp ρ =
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).comp
        f.appTop.hom) :
    (continuousHomOfComp O ρ hρ I f hf φ hφc hφ).toRingHom = φ := rfl

include hρ hf in
/-- **A continuous map `B → A^∧` over `S` is `R`-linear** when the stages of `B` lie over `O`
through `ρ : R → B` and `V` lies over `O` through `f`: on every stage `A^∧ ⧸ I^{n+1} A^∧` the two
maps `R → A^∧ ⧸ I^{n+1} A^∧` induce the same morphism to `O ≅ Spec R`, and `A^∧` is
`I`-adically separated. -/
theorem toRingHom_comp_eq_of_isOver [IsTopologicalRing Bt] [IsLinearTopology Bt Bt]
    (hB : TopologicalRing.IsWeaklyAdmissible Bt)
    (φ : FormalSpace.ContinuousHom DB (completionQuotientSystem V I)) :
    φ.toRingHom.comp ρ =
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).comp
        f.appTop.hom := by
  classical
  obtain ⟨hTR, -, hIadic, -, -⟩ :=
    FormalSpace.adicCompletion_isAdic_of_fg I I.fg_of_isNoetherianRing
  set Ah := AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  set L := I.map (algebraMap _ Ah)
  obtain ⟨J₀, hJ₀⟩ := hB.1
  have hstage :
      ∀ n : ℕ, ∀ r, φ.toRingHom (ρ r) - algebraMap _ Ah (f.appTop.hom r) ∈ L ^ (n + 1) := by
    intro n r
    let K : { K : Ideal Ah // TopologicalRing.IsWeakIdealOfDefinition K } :=
      ⟨L ^ (n + 1), TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hIadic n⟩
    let J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J } :=
      ⟨J₀ ⊓ Ideal.comap φ.toRingHom K.1, by
        refine ⟨?_, fun x hx => hJ₀.2 x (Ideal.mem_inf.mp hx).1⟩
        show IsOpen ((J₀ : Set Bt) ∩ φ.toRingHom ⁻¹' (K.1 : Set Ah))
        exact hJ₀.1.inter (K.2.1.preimage φ.continuous)⟩
    have h1 := φ.overS J K inf_le_right
    change _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K.1).comp (algebraMap _ Ah))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom at h1
    rw [hρ J, spec_map_comp_isoSpec_inv_comp_eq f hf, ← Spec.map_comp_assoc,
      cancel_mono] at h1
    have h2 := congrArg (fun g => (g.hom r)) (Spec.map_injective h1)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Ideal.quotientMap_mk] at h2
    exact Ideal.Quotient.eq.mp h2
  refine RingHom.ext fun r => ?_
  refine sub_eq_zero.mp
    ((AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing).toIsHausdorff.haus _
      fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ n => exact hstage n r

end FormalDictionary

end AlgebraicGeometry.Artin

end
