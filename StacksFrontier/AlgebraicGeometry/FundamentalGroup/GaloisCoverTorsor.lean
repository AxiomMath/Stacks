module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois

/-!
# Torsors with a section

Let `π : P ⟶ T` carry a right action of a finite group `G` over `T` whose comparison map
`G × P ⟶ P ×_T P` is an isomorphism. A section `s` of the base change of `π` along `s ≫ π`
trivialises it: the `G`-translates of `s` identify `∐_G W` with `W ×_T P`. Consequently the
lifts of a morphism to `T` through `π` form a `G`-torsor.

## Main results

* `AlgebraicGeometry.Abhyankar.isIso_sigmaDesc_translateSection`: a torsor with a section is
  trivial.
* `AlgebraicGeometry.Abhyankar.exists_iso_sigma_of_lift`: the fibre of a torsor at a liftable
  point is a disjoint union of copies of that point.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Abhyankar

section Torsor

variable {G : Type v} [Group G] [Finite G] {P T W : Scheme.{u}} (π : P ⟶ T)
  (a : Gᵐᵒᵖ →* Aut (Over.mk π)) (s : W ⟶ P)

omit [Finite G] in
/-- Each automorphism `a (op σ)` of `π` lies over `T`. -/
lemma twist_comp_eq (σ : G) : (a (.op σ)).asIso.hom.left ≫ π = π := Over.w (a (.op σ)).asIso.hom

/-- The `σ`-translate of a section `s` of the base change of `π` along `s ≫ π`. -/
def translateSection (σ : G) : W ⟶ pullback (s ≫ π) π :=
  pullback.lift (𝟙 W) (s ≫ (a (.op σ)).asIso.hom.left) (by
    rw [Category.id_comp, Category.assoc, twist_comp_eq])

omit [Finite G] in
/-- The square exhibiting the `σ`-translate of `s` as the base change of the graph of `σ`. -/
lemma isPullback_translateSection (σ : G) :
    IsPullback (translateSection π a s σ) s
      (pullback.map (s ≫ π) π π π s (𝟙 P) (𝟙 T) (by simp) (by simp))
      (pullback.lift (𝟙 P) (a (.op σ)).asIso.hom.left (by
        rw [Category.id_comp, twist_comp_eq])) := by
  let m := pullback.map (s ≫ π) π π π s (𝟙 P) (𝟙 T) (by simp) (by simp)
  have hright : IsPullback (pullback.fst (s ≫ π) π) m s (pullback.fst π π) := by
    have hm : m ≫ pullback.snd π π = pullback.snd (s ≫ π) π := by
      simp only [m, pullback.map, pullback.lift_snd, Category.comp_id]
    have hm' : m ≫ pullback.fst π π = pullback.fst (s ≫ π) π ≫ s := by
      simp only [m, pullback.map, pullback.lift_fst]
    have hbig : IsPullback (m ≫ pullback.snd π π) (pullback.fst (s ≫ π) π) π (s ≫ π) :=
      hm ▸ (IsPullback.of_hasPullback (s ≫ π) π).flip
    exact (IsPullback.of_right hbig hm' (IsPullback.of_hasPullback π π).flip).flip
  have hw : translateSection π a s σ ≫ m =
      s ≫ pullback.lift (𝟙 P) (a (.op σ)).asIso.hom.left (by rw [Category.id_comp, twist_comp_eq]) := by
    apply pullback.hom_ext
    · simp only [translateSection, m, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
    · simp only [translateSection, m, pullback.map, Category.assoc, pullback.lift_snd,
        Category.comp_id]
  have ho : IsPullback (translateSection π a s σ ≫ pullback.fst (s ≫ π) π) s s
      (pullback.lift (𝟙 P) (a (.op σ)).asIso.hom.left (by rw [Category.id_comp, twist_comp_eq]) ≫
        pullback.fst π π) := by
    rw [translateSection, pullback.lift_fst, pullback.lift_fst]
    exact IsPullback.id_horiz s
  exact ho.of_right hw hright

/-- **A torsor with a section is trivial.** If `π` is a `G`-torsor (its comparison map is an
isomorphism), then for every `s : W ⟶ P` the translates of `s` identify `∐_G W` with the base
change of `π` along `s ≫ π`. -/
theorem isIso_sigmaDesc_translateSection
    [IsIso (Stacks.Descent.galoisCoverComparison π a)] :
    IsIso (Limits.Sigma.desc (translateSection π a s)) := by
  let c := Cofan.mk (pullback π π) (fun σ : G ↦ pullback.lift (𝟙 P) (a (.op σ)).asIso.hom.left (by
    rw [Category.id_comp, twist_comp_eq]))
  have hc : Nonempty (IsColimit c) := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc c).mpr
    ‹IsIso (Stacks.Descent.galoisCoverComparison π a)›
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ (translateSection π a s))).mp
    (FinitaryPreExtensive.isUniversal_finiteCoproducts hc.some _ (Discrete.natTrans fun _ ↦ s)
      (pullback.map (s ≫ π) π π π s (𝟙 P) (𝟙 T) (by simp) (by simp)) ?_ (.of_discrete _) ?_)
  · ext ⟨σ⟩
    exact (isPullback_translateSection π a s σ).w.symm
  · rintro ⟨σ⟩
    exact isPullback_translateSection π a s σ

/-- Projecting the translates of `s` to `W` gives the codiagonal map. -/
private theorem sigmaDesc_translateSection_fst :
    Limits.Sigma.desc (translateSection π a s) ≫ pullback.fst (s ≫ π) π =
      Limits.Sigma.desc (fun _ : G ↦ 𝟙 W) := by
  apply Sigma.hom_ext
  intro σ
  simp only [Sigma.ι_desc_assoc, translateSection, pullback.lift_fst, Limits.Sigma.ι_desc]

/-- **The fibre of a torsor at a point that lifts is a disjoint union of copies of the point.**
If `π` is a `G`-torsor over `T`, `i : T ⟶ X` is a monomorphism and `w : W ⟶ X` lifts to `P`,
then `W ×_X P` is a disjoint union of copies of `W`, indexed by a type in the universe of the
schemes. -/
theorem exists_iso_sigma_of_lift [IsIso (Stacks.Descent.galoisCoverComparison π a)]
    {X : Scheme.{u}} (i : T ⟶ X) [Mono i] (w : W ⟶ X) (hs : s ≫ π ≫ i = w) :
    ∃ (J : Type u) (eJ : pullback w (π ≫ i) ≅ ∐ fun _ : J ↦ W),
      eJ.hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 W) = pullback.fst _ _ := by
  classical
  rw [← Category.assoc] at hs
  subst hs
  obtain ⟨n, ⟨eG⟩⟩ := Finite.exists_equiv_fin G
  let e : ULift.{u} (Fin n) ≃ G := Equiv.ulift.trans eG.symm
  have := isIso_sigmaDesc_translateSection π a s
  have hpb : IsPullback (pullback.fst (s ≫ π) π) (pullback.snd (s ≫ π) π) ((s ≫ π) ≫ i)
      (π ≫ i) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono (s ≫ π) π i)
  let E1 : pullback ((s ≫ π) ≫ i) (π ≫ i) ≅ pullback (s ≫ π) π := hpb.isoPullback.symm
  let E2 : (∐ fun _ : G ↦ W) ≅ pullback (s ≫ π) π :=
    asIso (Limits.Sigma.desc (translateSection π a s))
  let E3 : (∐ fun _ : ULift.{u} (Fin n) ↦ W) ≅ ∐ fun _ : G ↦ W :=
    Sigma.whiskerEquiv e (fun _ ↦ Iso.refl W)
  refine ⟨ULift.{u} (Fin n), E1 ≪≫ E2.symm ≪≫ E3.symm, ?_⟩
  have h2 : E2.hom ≫ pullback.fst (s ≫ π) π = Limits.Sigma.desc (fun _ ↦ 𝟙 W) :=
    sigmaDesc_translateSection_fst π a s
  have h3 : E3.inv ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 W) = Limits.Sigma.desc (fun _ ↦ 𝟙 W) := by
    apply Sigma.hom_ext
    intro σ
    simp [E3, Sigma.whiskerEquiv]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, h3]
  rw [← h2, Iso.inv_hom_id_assoc]
  exact hpb.isoPullback_inv_fst

/-- **The lifts through a torsor form a torsor.** If `π` is a `G`-torsor and `W` has exactly one
point, then every lift `t` of `s ≫ π` through `π` is the translate of `s` by a unique `σ ∈ G`. -/
theorem existsUnique_comp_twist [IsIso (Stacks.Descent.galoisCoverComparison π a)]
    [Subsingleton W] [Nonempty W] (t : W ⟶ P) (ht : t ≫ π = s ≫ π) :
    ∃! σ : G, s ≫ (a (.op σ)).asIso.hom.left = t := by
  classical
  have := isIso_sigmaDesc_translateSection π a s
  let E := asIso (Limits.Sigma.desc (translateSection π a s))
  have hE : E.hom ≫ pullback.fst (s ≫ π) π = Limits.Sigma.desc (fun _ : G ↦ 𝟙 W) :=
    sigmaDesc_translateSection_fst π a s
  let u : W ⟶ pullback (s ≫ π) π := pullback.lift (𝟙 W) t (by rw [Category.id_comp, ht])
  let u' := u ≫ E.inv
  have hu' : u' ≫ Limits.Sigma.desc (fun _ : G ↦ 𝟙 W) = 𝟙 W := by
    rw [← hE, Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.lift_fst _ _ _
  obtain ⟨w0⟩ := (inferInstance : Nonempty W)
  obtain ⟨σ, w1, hσ⟩ : ∃ (σ : G) (w1 : W), Sigma.ι (fun _ : G ↦ W) σ w1 = u' w0 :=
    (sigmaOpenCover (fun _ : G ↦ W)).exists_eq (u' w0)
  have hrange : Set.range u' ⊆ Set.range (Sigma.ι (fun _ : G ↦ W) σ) := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w w0]
    exact ⟨w1, hσ⟩
  let l := IsOpenImmersion.lift (Sigma.ι (fun _ : G ↦ W) σ) u' hrange
  have hl : l ≫ Sigma.ι (fun _ : G ↦ W) σ = u' := IsOpenImmersion.lift_fac _ _ _
  have hl1 : l = 𝟙 W := by
    simpa [hu'] using hl =≫ Limits.Sigma.desc (fun _ : G ↦ 𝟙 W)
  have hu : u = translateSection π a s σ := by
    have h1 : u = u' ≫ E.hom := by simp [u']
    rw [h1, ← hl, hl1, Category.id_comp]
    simp only [E, asIso_hom]
    exact Limits.Sigma.ι_desc _ _
  refine ⟨σ, ?_, fun τ hτ ↦ ?_⟩
  · have := congrArg (· ≫ pullback.snd (s ≫ π) π) hu
    simp only [u, translateSection, pullback.lift_snd] at this
    exact this.symm
  · have hτu : translateSection π a s τ = u := by
      apply pullback.hom_ext
      · simp only [translateSection, u, pullback.lift_fst]
      · simp only [translateSection, u, pullback.lift_snd, hτ]
    have hιE : Sigma.ι (fun _ : G ↦ W) τ ≫ E.hom = Sigma.ι (fun _ : G ↦ W) σ ≫ E.hom := by
      simp only [E, asIso_hom]
      rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, hτu, hu]
    have hι := (cancel_mono E.hom).mp hιE
    have := congrArg (fun g ↦ g w0) hι
    simp only at this
    have := (sigmaι_eq_iff (fun _ : G ↦ W) τ σ w0 w0).mp this
    exact (Sigma.mk.inj_iff.mp this).1

end Torsor

end AlgebraicGeometry.Abhyankar
