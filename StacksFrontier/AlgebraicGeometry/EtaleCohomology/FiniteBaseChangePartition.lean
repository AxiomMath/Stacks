module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Bijectivity

/-!
# Étale neighbourhoods partitioning the base change of a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and `y` a geometric point of `Y`, with lifts
`x₁, …, xₙ` to `X`. Suppose each lift is given an étale neighbourhood `aᵢ : Uᵢ ⟶ X`. Then there
is an affine étale neighbourhood `e : V ⟶ Y` of `y` over which the base change `X ×_Y V` is the
disjoint union of open subschemes `Nᵢ`, the `i`-th one containing the lift of `xᵢ` and mapping to
`Uᵢ` over `X`, compatibly with the points.

## Main results

* `AlgebraicGeometry.exists_etale_partition_refining_of_isFinite`: the partition.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Étale neighbourhoods partitioning the base change of a finite morphism.** Let `f : X ⟶ Y`
be finite, `y` a geometric point of `Y` and `Λ : I → {lifts of y}` a bijection. For every
`i : I` let `aᵢ : Uᵢ ⟶ X` be étale with a lift `wᵢ` of the lift `Λ i`. Then there are an affine
scheme `V`, an étale `e : V ⟶ Y` with a lift `q` of `y`, and pairwise disjoint opens `Nᵢ` covering
`X ×_Y V`, each with a morphism `bᵢ : Nᵢ ⟶ Uᵢ` over `X` and a point `n` over `(Λ i, q)` sent by
`bᵢ` to `wᵢ`. -/
theorem exists_etale_partition_refining_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) {I : Type*}
    (Λ : I → {g : y.source ⟶ X // g ≫ f = y.hom}) (hΛ : Function.Bijective Λ)
    (U : I → Scheme.{u}) (a : ∀ i, U i ⟶ X) [∀ i, Etale (a i)]
    (w : ∀ i, y.source ⟶ U i) (hw : ∀ i, w i ≫ a i = (Λ i).1) :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (e : V ⟶ Y) (_ : Etale e) (q : y.source ⟶ V)
      (_ : q ≫ e = y.hom) (N : I → (pullback f e).Opens) (b : ∀ i, (N i).toScheme ⟶ U i),
      (∀ i, b i ≫ a i = (N i).ι ≫ pullback.fst f e) ∧
      (∀ i, ∃ n : y.source ⟶ N i, n ≫ (N i).ι ≫ pullback.fst f e = (Λ i).1 ∧
          n ≫ (N i).ι ≫ pullback.snd f e = q ∧ n ≫ b i = w i) ∧
      Pairwise (fun i j => Disjoint (N i).1 (N j).1) ∧
      ∀ z : (pullback f e : Scheme.{u}), ∃ i, z ∈ N i := by
  classical
  have : Finite I := Finite.of_injective Λ hΛ.1
  let _ : Fintype I := Fintype.ofFinite I
  choose V₁ g₁ hg₁ W₁ W₁' e₁ h₁ u₁ hh₁ hu₁ using fun i ↦ exists_etale_coprod_lift f (a i) (w i)
  obtain ⟨S₀, g₀, hg₀, p₀, hp₀, I₀, hI₀, D, hdis, hcov, -, hsingle⟩ :=
    exists_etale_partition_subsingleton_geometric_fibers f y
  let k₁ (i : I) : y.source ⟶ V₁ i := u₁ i ≫ coprod.inl ≫ (e₁ i).hom ≫ pullback.snd f (g₁ i)
  have hk₁ (i : I) : k₁ i ≫ g₁ i = y.hom := by
    calc k₁ i ≫ g₁ i = u₁ i ≫ (coprod.inl ≫ (e₁ i).hom ≫ pullback.fst f (g₁ i)) ≫ f := by
          simp only [k₁, Category.assoc, pullback.condition]
      _ = (u₁ i ≫ h₁ i) ≫ a i ≫ f := by rw [← hh₁ i]; simp only [Category.assoc]
      _ = y.hom := by rw [hu₁ i, ← Category.assoc, hw i]; exact (Λ i).2
  let E := (Scheme.pointSmallEtale y.hom).fiber.Elements
  let N₁ (i : I) : E := Functor.elementsMk _
    (MorphismProperty.Over.mk _ (g₁ i) (hg₁ i)) (Over.homMk (k₁ i) (hk₁ i))
  let N₀ : E := Functor.elementsMk _ (MorphismProperty.Over.mk _ g₀ hg₀) (Over.homMk p₀ hp₀)
  obtain ⟨M, hM⟩ := IsCofiltered.inf_objs_exists (insert N₀ (Finset.univ.image N₁))
  obtain ⟨v₀⟩ := hM (Finset.mem_insert_self _ _)
  have hv₁ (i : I) : Nonempty (M ⟶ N₁ i) :=
    hM (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  let v₁ (i : I) : M ⟶ N₁ i := Classical.choice (hv₁ i)
  let T : Scheme.{u} := M.obj.left
  let e : T ⟶ Y := M.obj.hom
  have : Etale e := M.obj.prop
  let q : y.source ⟶ T := M.val.left
  have hq : q ≫ e = y.hom := Over.w M.val
  let β₀ : T ⟶ S₀ := v₀.hom.left
  have hβ₀ : β₀ ≫ g₀ = e := v₀.hom.w
  have hqβ₀ : q ≫ β₀ = p₀ := congrArg (fun a ↦ a.left) v₀.map_val
  let β₁ (i : I) : T ⟶ V₁ i := (v₁ i).hom.left
  have hβ₁ (i : I) : β₁ i ≫ g₁ i = e := (v₁ i).hom.w
  have hqβ₁ (i : I) : q ≫ β₁ i = k₁ i := congrArg (fun a ↦ a.left) (v₁ i).map_val
  let ρ₀ : pullback f e ⟶ pullback f g₀ :=
    pullback.map f e f g₀ (𝟙 X) β₀ (𝟙 Y) (by simp) (by simp [hβ₀])
  let ρ₁ (i : I) : pullback f e ⟶ pullback f (g₁ i) :=
    pullback.map f e f (g₁ i) (𝟙 X) (β₁ i) (𝟙 Y) (by simp) (by simp [hβ₁ i])
  let ℓ (i : I) : y.source ⟶ pullback f e := pullback.lift (Λ i).1 q ((Λ i).2.trans hq.symm)
  have hℓ₁ (i : I) : ℓ i ≫ ρ₁ i = u₁ i ≫ coprod.inl ≫ (e₁ i).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ρ₁, ℓ, pullback.lift_fst, Category.comp_id]
      rw [← hh₁ i, ← Category.assoc, hu₁ i, hw i]
    · simp only [Category.assoc, ρ₁, ℓ, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hqβ₁ i
  have hℓ₀ (i : I) : ℓ i ≫ ρ₀ ≫ pullback.snd f g₀ = p₀ := by
    simpa only [ρ₀, ℓ, pullback.lift_snd, pullback.lift_snd_assoc] using hqβ₀
  have hℓfst (i : I) : ℓ i ≫ ρ₀ ≫ pullback.fst f g₀ = (Λ i).1 := by
    simp only [ρ₀, ℓ, pullback.lift_fst, Category.comp_id]
  have hrange {Z : Scheme.{u}} (W : Z.Opens) (g : y.source ⟶ Z) (h : g default ∈ W) :
      Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨g p, ?_⟩, rfl⟩
    rwa [Subsingleton.elim p (default : y.source)]
  have hmemD (i : I) : ∃ k, (ℓ i ≫ ρ₀) default ∈ D k :=
    Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov ((ℓ i ≫ ρ₀) default))
  choose κ hκ using hmemD
  have hκinj : Function.Injective κ := by
    intro i j hij
    have hr (i' : I) (hi' : κ i' = κ i) :
        Set.range (ℓ i' ≫ ρ₀) ⊆ Set.range (D (κ i)).ι :=
      hrange _ _ (hi' ▸ hκ i')
    have hl (i' : I) (hi' : κ i' = κ i) :
        IsOpenImmersion.lift (D (κ i)).ι (ℓ i' ≫ ρ₀) (hr i' hi') ≫ (D (κ i)).ι = ℓ i' ≫ ρ₀ :=
      IsOpenImmersion.lift_fac _ _ _
    have hel := (hsingle (κ i)).elim
      ⟨IsOpenImmersion.lift (D (κ i)).ι (ℓ i ≫ ρ₀) (hr i rfl), by
        rw [← Category.assoc, hl i rfl, Category.assoc, hℓ₀ i]⟩
      ⟨IsOpenImmersion.lift (D (κ i)).ι (ℓ j ≫ ρ₀) (hr j hij.symm), by
        rw [← Category.assoc, hl j hij.symm, Category.assoc, hℓ₀ j]⟩
    have h' : ℓ i ≫ ρ₀ = ℓ j ≫ ρ₀ := by
      rw [← hl i rfl, ← hl j hij.symm]
      exact congrArg (fun m ↦ m ≫ (D (κ i)).ι) (congrArg Subtype.val hel)
    apply hΛ.1
    apply Subtype.ext
    rw [← hℓfst i, ← hℓfst j, ← Category.assoc, h', Category.assoc]
  let O (i : I) : (pullback f e).Opens :=
    (ρ₁ i) ⁻¹ᵁ (coprod.inl ≫ (e₁ i).hom).opensRange ⊓ ρ₀ ⁻¹ᵁ D (κ i)
  have hℓO (i : I) : (ℓ i) default ∈ O i := by
    refine ⟨?_, hκ i⟩
    change (ρ₁ i) ((ℓ i) default) ∈ Set.range (coprod.inl ≫ (e₁ i).hom)
    refine ⟨u₁ i default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hℓ₁ i, Scheme.Hom.comp_apply]
  have hOdis : Pairwise fun i j ↦ Disjoint (O i).1 (O j).1 := by
    intro i j hij
    exact Set.disjoint_left.mpr fun z hz hz' ↦ Set.disjoint_left.mp
      (hdis (Set.mem_univ _) (Set.mem_univ _) (fun h ↦ hij (hκinj h))) hz.2 hz'.2
  let yq : GeometricPoint T := { residueField := y.residueField, hom := q }
  obtain ⟨O', hqO', hO'⟩ := exists_open_base_of_geometricLifts (pullback.snd f e) yq
    (⨆ i, O i) (by
      intro l
      obtain ⟨i, hi⟩ := hΛ.2 ⟨l.1 ≫ pullback.fst f e, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, l.2]
        exact hq⟩
      have hl : l.1 = ℓ i := by
        apply pullback.hom_ext
        · simp only [ℓ, pullback.lift_fst]
          exact (congrArg Subtype.val hi).symm
        · simp only [ℓ, pullback.lift_snd]
          exact l.2
      rw [hl]
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hℓO i⟩)
  obtain ⟨A, hA, hqA, hAO'⟩ := exists_isAffineOpen_mem_and_subset hqO'
  have : IsAffine A.toScheme := hA
  let q' : y.source ⟶ A.toScheme := IsOpenImmersion.lift A.ι q (hrange _ _ hqA)
  have hq' : q' ≫ A.ι = q := IsOpenImmersion.lift_fac _ _ _
  let e' : A.toScheme ⟶ Y := A.ι ≫ e
  have hq'e : q' ≫ e' = y.hom := by rw [← Category.assoc, hq', hq]
  let τ : pullback f e' ⟶ pullback f e :=
    pullback.map f e' f e (𝟙 X) A.ι (𝟙 Y) (by simp) (by simp [e'])
  let N (i : I) : (pullback f e').Opens := τ ⁻¹ᵁ O i
  have hψ (i : I) : Set.range ((N i).ι ≫ τ ≫ ρ₁ i) ⊆ Set.range (coprod.inl ≫ (e₁ i).hom) := by
    rintro _ ⟨z, rfl⟩
    exact z.2.1
  let c (i : I) : (N i).toScheme ⟶ W₁ i :=
    IsOpenImmersion.lift (coprod.inl ≫ (e₁ i).hom) ((N i).ι ≫ τ ≫ ρ₁ i) (hψ i)
  have hc (i : I) : c i ≫ coprod.inl ≫ (e₁ i).hom = (N i).ι ≫ τ ≫ ρ₁ i :=
    IsOpenImmersion.lift_fac _ _ _
  let ℓ' (i : I) : y.source ⟶ pullback f e' := pullback.lift (Λ i).1 q' ((Λ i).2.trans hq'e.symm)
  have hℓ' (i : I) : ℓ' i ≫ τ = ℓ i := by
    apply pullback.hom_ext
    · simp only [Category.assoc, τ, ℓ', ℓ, pullback.lift_fst, Category.comp_id]
    · simp only [Category.assoc, τ, ℓ', ℓ, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hq'
  have hℓ'r (i : I) : Set.range (ℓ' i) ⊆ Set.range (N i).ι := by
    refine hrange _ _ ?_
    change τ (ℓ' i default) ∈ O i
    rw [← Scheme.Hom.comp_apply, hℓ' i]
    exact hℓO i
  refine ⟨A.toScheme, inferInstance, e', inferInstance, q', hq'e, N, fun i ↦ c i ≫ h₁ i,
    fun i ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_, fun z ↦ ?_⟩
  · rw [Category.assoc, hh₁ i, reassoc_of% (hc i)]
    simp only [τ, ρ₁, pullback.lift_fst, Category.comp_id]
  · let n := IsOpenImmersion.lift (N i).ι (ℓ' i) (hℓ'r i)
    have hn : n ≫ (N i).ι = ℓ' i := IsOpenImmersion.lift_fac _ _ _
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [reassoc_of% hn]
      simp only [ℓ', pullback.lift_fst]
    · rw [reassoc_of% hn]
      simp only [ℓ', pullback.lift_snd]
    · have hnc : n ≫ c i = u₁ i := by
        rw [← cancel_mono (coprod.inl ≫ (e₁ i).hom), Category.assoc, hc i, reassoc_of% hn,
          reassoc_of% (hℓ' i), hℓ₁ i]
      rw [← Category.assoc, hnc, hu₁ i]
  · exact Set.disjoint_left.mpr fun z hz hz' ↦
      Set.disjoint_left.mp (hOdis hij) (show τ z ∈ O i from hz) (show τ z ∈ O j from hz')
  · have hz : τ z ∈ (pullback.snd f e) ⁻¹' (O' : Set T) := by
      change (pullback.snd f e) (τ z) ∈ O'
      rw [← Scheme.Hom.comp_apply]
      have hτ : τ ≫ pullback.snd f e = pullback.snd f e' ≫ A.ι := by
        simp only [τ, pullback.lift_snd]
      rw [hτ, Scheme.Hom.comp_apply]
      exact hAO' (pullback.snd f e' z).2
    exact (TopologicalSpace.Opens.mem_iSup (s := O)).mp (hO' hz)

end AlgebraicGeometry
