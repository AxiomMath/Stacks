module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.PieceHomExt

/-!
# Equivariant morphisms of finite étale covers descend to a finite stage

Let `Y` be a scheme over a field `k`, `K/k` an algebraic extension and `Y_K = Y ×_k K`. Let
`Q₁, Q₂` be finite étale covers of `Y` with endomorphisms `τ₁, τ₂`. A morphism
`Q₁ ×_Y Y_K ⟶ Q₂ ×_Y Y_K` of covers of `Y_K` commuting with the base changes of the `τ`'s is, at
some finite subextension `E`, the base change of a morphism `Q₁ ×_Y Y_E ⟶ Q₂ ×_Y Y_E` commuting
with the `τ`'s. This is Tag 0BTV for the limit `Y_K = lim Y_E`
(`AlgebraicGeometry.exists_finiteEtale_hom_model`), applied to the morphism and to the equations
it satisfies.

## Main results

* `AlgebraicGeometry.exists_stage_hom_of_baseChange`: an equivariant morphism of the base
  changes to `Y_K` of finite étale covers of `Y` comes from one at a finite stage `Y_E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- If `Φ : F.obj A ⟶ F.obj B` satisfies `F.map τA ≫ Φ = Φ ≫ F.map τB`, then its conjugate
`α.inv.app A ≫ Φ ≫ α.hom.app B` by an isomorphism `α : F ≅ G` satisfies the same relation for `G`.
-/
theorem comm_conj_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ≅ G)
    {A B : C} (τA : A ⟶ A) (τB : B ⟶ B) (Φ : F.obj A ⟶ F.obj B)
    (hΦ : F.map τA ≫ Φ = Φ ≫ F.map τB) :
    G.map τA ≫ (α.inv.app A ≫ Φ ≫ α.hom.app B) = (α.inv.app A ≫ Φ ≫ α.hom.app B) ≫ G.map τB := by
  calc G.map τA ≫ α.inv.app A ≫ Φ ≫ α.hom.app B = α.inv.app A ≫ F.map τA ≫ Φ ≫ α.hom.app B := by
        rw [← α.inv.naturality_assoc]
    _ = α.inv.app A ≫ Φ ≫ F.map τB ≫ α.hom.app B := by rw [reassoc_of% hΦ]
    _ = _ := by
      rw [α.hom.naturality]
      simp only [Category.assoc]

/-- A functor preserves the relation `τA ≫ Φ = Φ ≫ τB`. -/
theorem comm_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B : C} (τA : A ⟶ A)
    (τB : B ⟶ B) (Φ : A ⟶ B) (hΦ : τA ≫ Φ = Φ ≫ τB) : F.map τA ≫ F.map Φ = F.map Φ ≫ F.map τB := by
  rw [← F.map_comp, hΦ, F.map_comp]

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  {Y : Scheme.{u}} (r : Y ⟶ Spec (.of k))

omit [Algebra.IsAlgebraic k K] in
/-- The transition maps `Y ×_k E_i ⟶ Y ×_k E_j` of `fextPullbackDiagram` commute with the
projections to `Y`. -/
theorem fextPullbackDiagram_map_snd {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j) :
    (fextPullbackDiagram (k := k) (K := K) Y r).map g ≫ pullback.snd (spectrumMap k j.unop.1) r =
      pullback.snd (spectrumMap k i.unop.1) r := by
  dsimp [fextPullbackDiagram, fextOverDiagram]
  simp only [Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

/-- The projections `Y ×_k K ⟶ Y ×_k E_i` of `fextPullbackCone` commute with the projections
to `Y`. -/
theorem fextPullbackCone_π_snd (i : (FExt k K)ᵒᵖ) :
    (fextPullbackCone (k := k) (K := K) Y r).π.app i ≫ pullback.snd (spectrumMap k i.unop.1) r =
      pullback.snd (spectrumMap k K) r := by
  dsimp [fextPullbackCone, fextPullbackDiagram, fextOverCone, fextOverDiagram]
  simp only [Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

/-- **Equivariant morphisms of finite étale covers descend to a finite stage.** A morphism
`Q₁ ×_Y Y_K ⟶ Q₂ ×_Y Y_K` commuting with the base changes of the endomorphisms `τ₁ a, τ₂ a` comes
from a morphism `Q₁ ×_Y Y_E ⟶ Q₂ ×_Y Y_E` commuting with them, for some finite subextension `E`
of `K/k`. -/
theorem exists_stage_hom_of_baseChange [CompactSpace Y] [QuasiSeparatedSpace Y] {ι : Type*}
    [Finite ι] (Q₁ Q₂ : FiniteEtaleOver Y)
    (τ₁ : ι → (Q₁ ⟶ Q₁)) (τ₂ : ι → (Q₂ ⟶ Q₂))
    (Φ : (finiteEtaleBaseChange (pullback.fst r (spectrumMap k K))).obj Q₁ ⟶
      (finiteEtaleBaseChange (pullback.fst r (spectrumMap k K))).obj Q₂)
    (hΦ : ∀ a, (finiteEtaleBaseChange (pullback.fst r (spectrumMap k K))).map (τ₁ a) ≫ Φ =
      Φ ≫ (finiteEtaleBaseChange (pullback.fst r (spectrumMap k K))).map (τ₂ a)) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Ψ : (finiteEtaleBaseChange (pullback.snd (spectrumMap k E) r)).obj Q₁ ⟶
        (finiteEtaleBaseChange (pullback.snd (spectrumMap k E) r)).obj Q₂),
      ∀ a, (finiteEtaleBaseChange (pullback.snd (spectrumMap k E) r)).map (τ₁ a) ≫ Ψ =
        Ψ ≫ (finiteEtaleBaseChange (pullback.snd (spectrumMap k E) r)).map (τ₂ a) := by
  classical
  let D := fextPullbackDiagram (k := k) (K := K) Y r
  let c := fextPullbackCone (k := k) (K := K) Y r
  have hc : IsLimit c := fextPullbackConeIsLimit (k := k) (K := K) Y r
  have : ∀ {i j : (FExt k K)ᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) :=
    fun g => fextPullbackTransition_isAffineHom Y r g
  have : ∀ i : (FExt k K)ᵒᵖ, CompactSpace (D.obj i) := fun i =>
    inferInstanceAs (CompactSpace (pullback (spectrumMap k i.unop.1) r : Scheme.{u}))
  have : ∀ i : (FExt k K)ᵒᵖ, IsAffineHom (pullback.snd (spectrumMap k i.unop.1) r) :=
    fun i =>
      let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) r :=
        ⟨fun sq H => isAffineHom_isStableUnderBaseChange.of_isPullback sq H⟩
      MorphismProperty.pullback_snd _ _ inferInstance
  have : ∀ i : (FExt k K)ᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i =>
    have h1 : IsSeparated (pullback.snd (spectrumMap k i.unop.1) r) := IsSeparated.of_isAffineHom _
    have h2 : QuasiSeparated (pullback.snd (spectrumMap k i.unop.1) r) := inferInstance
    @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (spectrumMap k i.unop.1) r) _ h2
  let eK : pullback r (spectrumMap k K) ≅ c.pt := pullbackSymmetry r (spectrumMap k K)
  let sK := pullback.snd (spectrumMap k K) r
  let sE : ∀ i : (FExt k K)ᵒᵖ, D.obj i ⟶ Y := fun i => pullback.snd (spectrumMap k i.unop.1) r
  -- step 1: transport to the apex of the limit cone
  let α₁ := finiteEtaleBaseChangeComp eK.inv (pullback.fst r (spectrumMap k K)) sK
    (pullbackSymmetry_inv_comp_fst _ _).symm
  let ΨK := α₁.hom.app Q₁ ≫ (finiteEtaleBaseChange eK.inv).map Φ ≫ α₁.inv.app Q₂
  have hΨK : ∀ a, (finiteEtaleBaseChange sK).map (τ₁ a) ≫ ΨK =
      ΨK ≫ (finiteEtaleBaseChange sK).map (τ₂ a) := by
    intro a
    exact comm_conj_iso α₁.symm (τ₁ a) (τ₂ a) ((finiteEtaleBaseChange eK.inv).map Φ)
      (comm_map (finiteEtaleBaseChange eK.inv) _ _ _ (hΦ a))
  -- step 2: to the bottom stage
  let i₀ : (FExt k K)ᵒᵖ := op ⟨⊥, inferInstance⟩
  let A₁ := (finiteEtaleBaseChange (sE i₀)).obj Q₁
  let A₂ := (finiteEtaleBaseChange (sE i₀)).obj Q₂
  let α₂ := finiteEtaleBaseChangeComp (c.π.app i₀) (sE i₀) sK
    (fextPullbackCone_π_snd k K r i₀).symm
  let ψ' : (finiteEtaleBaseChange (c.π.app i₀)).obj A₁ ⟶
      (finiteEtaleBaseChange (c.π.app i₀)).obj A₂ := α₂.inv.app Q₁ ≫ ΨK ≫ α₂.hom.app Q₂
  have hψ' : ∀ a, (finiteEtaleBaseChange (sE i₀) ⋙ finiteEtaleBaseChange (c.π.app i₀)).map
        (τ₁ a) ≫ ψ' =
      ψ' ≫ (finiteEtaleBaseChange (sE i₀) ⋙ finiteEtaleBaseChange (c.π.app i₀)).map (τ₂ a) :=
    fun a => comm_conj_iso α₂ (τ₁ a) (τ₂ a) ΨK (hΨK a)
  -- step 3: a model at some stage
  obtain ⟨j, e, χ, hχ⟩ := exists_finiteEtale_hom_model D c hc i₀ A₁ A₂ ψ'
  let L := finiteEtaleLimitCompIso D c e
  let τA₁ : ι → (A₁ ⟶ A₁) := fun a => (finiteEtaleBaseChange (sE i₀)).map (τ₁ a)
  let τA₂ : ι → (A₂ ⟶ A₂) := fun a => (finiteEtaleBaseChange (sE i₀)).map (τ₂ a)
  have hχL : L.inv.app A₁ ≫ ψ' ≫ L.hom.app A₂ = (finiteEtaleBaseChange (c.π.app j)).map χ := by
    rw [hχ]
    simp only [L, Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  have hχ' : ∀ a, (finiteEtaleBaseChange (c.π.app j)).map
        ((finiteEtaleBaseChange (D.map e)).map (τA₁ a) ≫ χ) =
      (finiteEtaleBaseChange (c.π.app j)).map
        (χ ≫ (finiteEtaleBaseChange (D.map e)).map (τA₂ a)) := by
    intro a
    have h2 := comm_conj_iso L (τA₁ a) (τA₂ a) ψ' (hψ' a)
    rw [hχL] at h2
    simpa only [Functor.map_comp, Functor.comp_map] using h2
  -- step 4: the equations hold at a common later stage
  choose j' e' he' using fun a =>
    eventually_eq_of_finiteEtaleBaseChange_eq D c hc j _ _ _ _ (hχ' a)
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (insert j (Finset.univ.image fun a => j' a))
  let fS : S ⟶ j := (hS (Finset.mem_insert_self _ _)).some
  have hfS : ∀ a, (finiteEtaleBaseChange (D.map fS)).map
        ((finiteEtaleBaseChange (D.map e)).map (τA₁ a) ≫ χ) =
      (finiteEtaleBaseChange (D.map fS)).map
        (χ ≫ (finiteEtaleBaseChange (D.map e)).map (τA₂ a)) := by
    intro a
    let m : S ⟶ j' a := (hS (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ a)))).some
    have hm : fS = m ≫ e' a := Subsingleton.elim _ _
    refine Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.map_eq_of_iso
      (finiteEtaleBaseChangeComp (D.map m) (D.map (e' a)) (D.map fS)
        (by rw [hm, D.map_comp])).symm ?_
    change (finiteEtaleBaseChange (D.map m)).map ((finiteEtaleBaseChange (D.map (e' a))).map _) =
      (finiteEtaleBaseChange (D.map m)).map ((finiteEtaleBaseChange (D.map (e' a))).map _)
    rw [he' a]
  -- step 5: back to a base change of the covers of `Y`
  let β₁ := finiteEtaleBaseChangeComp (D.map e) (sE i₀) (sE j)
    (fextPullbackDiagram_map_snd k K r e).symm
  let β₂ := finiteEtaleBaseChangeComp (D.map fS) (sE j) (sE S)
    (fextPullbackDiagram_map_snd k K r fS).symm
  let γ := β₂ ≪≫ Functor.isoWhiskerRight β₁ (finiteEtaleBaseChange (D.map fS))
  refine ⟨S.unop.1, S.unop.2, γ.hom.app Q₁ ≫ (finiteEtaleBaseChange (D.map fS)).map χ ≫
    γ.inv.app Q₂, fun a => ?_⟩
  exact comm_conj_iso γ.symm (τ₁ a) (τ₂ a) _
    (by simpa only [Functor.map_comp, Functor.comp_map] using hfS a)

end AlgebraicGeometry
