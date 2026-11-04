module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Colimits of systems given by transition maps

Let `K` be a quiver, let `A i` be an object of a category `𝒞` for every vertex `i`, and for every
arrow `a : i ⟶ j` let `T a : A j ⟶ A i` be a map. No functoriality is asked of `T`: neither
`T (𝟙 i) = 𝟙` nor `T (a ≫ b) = T b ≫ T a` is required. This is the shape in which a *system* of
sheaves on an inverse system of sites appears in the Stacks project (Sites, Lemma 7.18.4,
[Stacks, Tag 0EZL]): the transition maps compose correctly only through comparison isomorphisms
of inverse images, so they do not form a functor on the nose.

A family `ψ i : A i ⟶ B` exhibits `B` as the *colimit of the system* when every family of maps
`τ i : A i ⟶ G` which is compatible with the transition maps, `T a ≫ τ i = τ j`, factors
uniquely through it. When `T` is a functor this is the universal property of a colimit cocone.

## Main definitions

* `CategoryTheory.Limits.IsSystemColimit` — the universal property above.

## Main results

* `CategoryTheory.Limits.IsSystemColimit.hom_ext` — maps out of a colimit of a system are
  determined by their composites with the legs.
* `CategoryTheory.Limits.IsSystemColimit.of_cokernel` — **cokernels commute with colimits of
  systems**: if at every vertex `C i` is a quotient of `B i` killing the image of `A i`, and if
  `𝒞` is the cokernel of the map `𝒜 ⟶ ℬ` between colimits of the systems `A` and `B`, then `𝒞`
  is a colimit of the system `C`. This is purely formal; no exactness of colimits is involved.
* `CategoryTheory.Limits.IsSystemColimit.isZero` — a colimit of a system of zero objects is
  zero.
* `CategoryTheory.Limits.IsSystemColimit.of_isIso` — over a directed set, a compatible family of
  isomorphisms exhibits its vertex as the colimit of the system.
* `CategoryTheory.Limits.IsSystemColimit.isIso_of_isIso_app` — a map of colimits of systems
  compatible with levelwise isomorphisms commuting with the transition maps is an isomorphism.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Limits

universe w₁ w₂ v u

variable {𝒞 : Type u} [Category.{v} 𝒞] {K : Type w₁} [Quiver.{w₂} K]

/-- **The colimit of a system given by transition maps.** The family `ψ i : A i ⟶ B` exhibits `B`
as the colimit of the system `(A, T)` when every family `τ i : A i ⟶ G` compatible with the
transition maps, `T a ≫ τ i = τ j` for every arrow `a : i ⟶ j`, factors uniquely through `ψ`. -/
def IsSystemColimit (A : K → 𝒞) (T : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i)) (B : 𝒞)
    (ψ : ∀ i, A i ⟶ B) : Prop :=
  ∀ (G : 𝒞) (τ : ∀ i, A i ⟶ G), (∀ {i j : K} (a : i ⟶ j), T a ≫ τ i = τ j) →
    ∃! χ : B ⟶ G, ∀ i, ψ i ≫ χ = τ i

namespace IsSystemColimit

variable {A : K → 𝒞} {T : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i)} {B : 𝒞} {ψ : ∀ i, A i ⟶ B}

/-- A family of maps compatible with `T'` stays compatible after precomposing with maps
commuting with the transition maps. -/
private theorem comp_compat {A' : K → 𝒞} {T' : ∀ {i j : K}, (i ⟶ j) → (A' j ⟶ A' i)} {G : 𝒞}
    {θ : ∀ i, A i ⟶ A' i} {τ : ∀ i, A' i ⟶ G}
    (hT : ∀ {i j : K} (a : i ⟶ j), T a ≫ θ i = θ j ≫ T' a)
    (hτ : ∀ {i j : K} (a : i ⟶ j), T' a ≫ τ i = τ j) :
    ∀ {i j : K} (a : i ⟶ j), T a ≫ θ i ≫ τ i = θ j ≫ τ j := by
  intro i j a
  rw [← Category.assoc, hT a, Category.assoc, hτ a]

/-- **Maps out of a colimit of a system are determined by the legs.** Two maps out of `B` that
agree after every leg `ψ i` are equal. This needs the legs to be compatible with the transition
maps, which they are in every colimit presentation. -/
theorem hom_ext (h : IsSystemColimit A T B ψ)
    (hψ : ∀ {i j : K} (a : i ⟶ j), T a ≫ ψ i = ψ j) {G : 𝒞} {χ₁ χ₂ : B ⟶ G}
    (hχ : ∀ i, ψ i ≫ χ₁ = ψ i ≫ χ₂) : χ₁ = χ₂ := by
  obtain ⟨χ, -, hu⟩ := h G (fun i => ψ i ≫ χ₂) (fun a => by
    rw [← Category.assoc, hψ a])
  exact (hu χ₁ hχ).trans (hu χ₂ fun _ => rfl).symm

/-- The factorization through a colimit of a system. -/
noncomputable def desc (h : IsSystemColimit A T B ψ) {G : 𝒞} (τ : ∀ i, A i ⟶ G)
    (hτ : ∀ {i j : K} (a : i ⟶ j), T a ≫ τ i = τ j) : B ⟶ G :=
  (h G τ hτ).choose

/-- The map `desc` out of a colimit of a system composes with each leg `ψ i` to `τ i`. -/
@[reassoc (attr := simp)]
theorem fac (h : IsSystemColimit A T B ψ) {G : 𝒞} (τ : ∀ i, A i ⟶ G)
    (hτ : ∀ {i j : K} (a : i ⟶ j), T a ≫ τ i = τ j) (i : K) :
    ψ i ≫ h.desc τ hτ = τ i :=
  (h G τ hτ).choose_spec.1 i

/-- A colimit of a system can be transported along an isomorphism of its vertex. -/
theorem of_iso (h : IsSystemColimit A T B ψ) {B' : 𝒞} (e : B ≅ B') :
    IsSystemColimit A T B' (fun i => ψ i ≫ e.hom) := by
  intro G τ hτ
  obtain ⟨χ, hχ, hu⟩ := h G τ hτ
  refine ⟨e.inv ≫ χ, fun i => by simp [hχ], fun χ' hχ' => ?_⟩
  exact e.eq_inv_comp.2 (hu _ fun i => by simpa using hχ' i)

/-- A colimit of a system is preserved by replacing the legs with equal ones. -/
theorem congr_legs (h : IsSystemColimit A T B ψ) {ψ' : ∀ i, A i ⟶ B} (hψ' : ∀ i, ψ i = ψ' i) :
    IsSystemColimit A T B ψ' := by
  have : ψ = ψ' := funext hψ'
  subst this
  exact h

/-- **A colimit of a system can be transported along an isomorphism of systems**: levelwise
isomorphisms `θ_i : A i ≅ A' i` commuting with the transition maps, and an isomorphism
`e : B ≅ B'` commuting with the legs, carry a colimit of `(A, T)` to a colimit of `(A', T')`. -/
theorem of_isoSystem (h : IsSystemColimit A T B ψ) {A' : K → 𝒞}
    {T' : ∀ {i j : K}, (i ⟶ j) → (A' j ⟶ A' i)} {B' : 𝒞} {ψ' : ∀ i, A' i ⟶ B'}
    (θ : ∀ i, A i ≅ A' i) (e : B ≅ B')
    (hT : ∀ {i j : K} (a : i ⟶ j), T a ≫ (θ i).hom = (θ j).hom ≫ T' a)
    (hψ : ∀ i, ψ i ≫ e.hom = (θ i).hom ≫ ψ' i) :
    IsSystemColimit A' T' B' ψ' := by
  intro G τ hτ
  obtain ⟨χ, hχ, hu⟩ := h G (fun i => (θ i).hom ≫ τ i) (comp_compat hT hτ)
  have hψ' : ∀ i, ψ' i = (θ i).inv ≫ ψ i ≫ e.hom := fun i => by
    rw [hψ i, Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ χ, fun i => ?_, fun χ' hχ' => ?_⟩
  · rw [hψ' i, Category.assoc, Category.assoc, e.hom_inv_id_assoc, hχ i, Iso.inv_hom_id_assoc]
  · exact e.eq_inv_comp.2 (hu _ fun i => by rw [← Category.assoc, hψ i, Category.assoc, hχ' i])

/-- **A map of colimits of systems which is an isomorphism at every level is an isomorphism.**
Let `(B, ψ)` and `(B', ψ')` be colimits of the systems `(A, T)` and `(A', T')`, let
`θ i : A i ⟶ A' i` be isomorphisms commuting with the transition maps, and let `β : B ⟶ B'` be
compatible with the legs. Then `β` is an isomorphism: its inverse is induced by the family
`θ i⁻¹ ≫ ψ i`. -/
theorem isIso_of_isIso_app (h : IsSystemColimit A T B ψ)
    (hψ : ∀ {i j : K} (a : i ⟶ j), T a ≫ ψ i = ψ j) {A' : K → 𝒞}
    {T' : ∀ {i j : K}, (i ⟶ j) → (A' j ⟶ A' i)} {B' : 𝒞} {ψ' : ∀ i, A' i ⟶ B'}
    (h' : IsSystemColimit A' T' B' ψ') (hψ' : ∀ {i j : K} (a : i ⟶ j), T' a ≫ ψ' i = ψ' j)
    (θ : ∀ i, A i ⟶ A' i) [∀ i, IsIso (θ i)]
    (hT : ∀ {i j : K} (a : i ⟶ j), T a ≫ θ i = θ j ≫ T' a) (β : B ⟶ B')
    (hβ : ∀ i, ψ i ≫ β = θ i ≫ ψ' i) : IsIso β := by
  have hT' : ∀ {i j : K} (a : i ⟶ j), T' a ≫ inv (θ i) ≫ ψ i = inv (θ j) ≫ ψ j := by
    refine comp_compat (θ := fun i => inv (θ i)) (fun {i j} a => ?_) hψ
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hT a, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  refine ⟨h'.desc (fun i => inv (θ i) ≫ ψ i) hT', h.hom_ext hψ fun i => ?_,
    h'.hom_ext hψ' fun i => ?_⟩
  · rw [reassoc_of% (hβ i), h'.fac, IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [reassoc_of% (h'.fac _ hT' i), hβ i, IsIso.inv_hom_id_assoc, Category.comp_id]

/-- **Left adjoints preserve colimits of systems.** -/
theorem map_of_isLeftAdjoint (h : IsSystemColimit A T B ψ) {𝒟 : Type*} [Category* 𝒟]
    {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) :
    IsSystemColimit (fun i ↦ L.obj (A i)) (fun a ↦ L.map (T a)) (L.obj B)
      (fun i ↦ L.map (ψ i)) := by
  intro G τ hτ
  have hτ' : ∀ {i j : K} (a : i ⟶ j), T a ≫ adj.homEquiv _ _ (τ i) = adj.homEquiv _ _ (τ j) :=
    fun a ↦ by rw [← Adjunction.homEquiv_naturality_left, hτ a]
  obtain ⟨χ, hχ, hu⟩ := h (R.obj G) (fun i ↦ adj.homEquiv _ _ (τ i)) hτ'
  refine ⟨(adj.homEquiv _ _).symm χ, fun i ↦ ?_, fun χ' hχ' ↦ ?_⟩
  · rw [← Adjunction.homEquiv_naturality_left_symm, hχ i, Equiv.symm_apply_apply]
  · exact Equiv.eq_symm_apply _ |>.2 (hu _ fun i ↦ by
      rw [← Adjunction.homEquiv_naturality_left, hχ' i])

/-- **Cokernels commute with colimits of systems.** Let `(A, T_A)`, `(B, T_B)`, `(C, T_C)` be
systems with maps `u i : A i ⟶ B i` and `v i : B i ⟶ C i` compatible with the transition maps, such
that at every vertex `u i ≫ v i = 0` and `v i` is an epimorphism. Let `(𝒜, α)` and `(ℬ, β)` be
colimits of the first two systems, let `U : 𝒜 ⟶ ℬ` and `V : ℬ ⟶ 𝒞'` be compatible with `u`, `v`
and maps `γ i : C i ⟶ 𝒞'`, and suppose that `V` is a cokernel of `U`. Then `γ` exhibits `𝒞'` as a
colimit of the third system.

No exactness of the colimits is involved: the argument only uses the two universal properties. -/
theorem of_cokernel [HasZeroMorphisms 𝒞] {A B C : K → 𝒞}
    {TA : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i)} {TB : ∀ {i j : K}, (i ⟶ j) → (B j ⟶ B i)}
    {TC : ∀ {i j : K}, (i ⟶ j) → (C j ⟶ C i)}
    (u : ∀ i, A i ⟶ B i) (v : ∀ i, B i ⟶ C i)
    (huv : ∀ i, u i ≫ v i = 0) (hv : ∀ i, Epi (v i))
    (hvT : ∀ {i j : K} (a : i ⟶ j), TB a ≫ v i = v j ≫ TC a)
    {𝒜 ℬ 𝒞' : 𝒞} {α : ∀ i, A i ⟶ 𝒜} {β : ∀ i, B i ⟶ ℬ} (γ : ∀ i, C i ⟶ 𝒞')
    (hA : IsSystemColimit A TA 𝒜 α) (hB : IsSystemColimit B TB ℬ β)
    (hα : ∀ {i j : K} (a : i ⟶ j), TA a ≫ α i = α j)
    (U : 𝒜 ⟶ ℬ) (V : ℬ ⟶ 𝒞') (hU : ∀ i, α i ≫ U = u i ≫ β i)
    (hV : ∀ i, β i ≫ V = v i ≫ γ i) {hUV : U ≫ V = 0}
    (hcok : IsColimit (CokernelCofork.ofπ V hUV)) :
    IsSystemColimit C TC 𝒞' γ := by
  intro G τ hτ
  -- the composite family `v i ≫ τ i` is compatible, hence factors through `ℬ`
  obtain ⟨χ', hχ', hu'⟩ := hB G (fun i => v i ≫ τ i) (comp_compat hvT hτ)
  -- it kills the image of `𝒜`
  have hz : U ≫ χ' = 0 := by
    obtain ⟨_, -, hu0⟩ := hA G (fun _ => 0) (fun _ => comp_zero)
    refine (hu0 _ fun i => ?_).trans (hu0 0 fun i => comp_zero).symm
    rw [← Category.assoc, hU i, Category.assoc, hχ' i, ← Category.assoc, huv i, zero_comp]
  set χ := hcok.desc (CokernelCofork.ofπ χ' hz) with hχdef
  have hVχ : V ≫ χ = χ' := hcok.fac (CokernelCofork.ofπ χ' hz) WalkingParallelPair.one
  refine ⟨χ, fun i => ?_, fun χ₁ hχ₁ => ?_⟩
  · rw [← cancel_epi (v i), ← Category.assoc, ← hV i, Category.assoc, hVχ, hχ' i]
  · have hV₁ : V ≫ χ₁ = χ' := hu' _ fun i => by
      rw [← Category.assoc, hV i, Category.assoc, hχ₁ i]
    have hepi : Epi V := epi_of_isColimit_cofork hcok
    rw [← cancel_epi V, hV₁, hVχ]

/-- **A colimit of a system of zero objects is zero.** -/
theorem isZero [HasZeroMorphisms 𝒞] (h : IsSystemColimit A T B ψ) (hA : ∀ i, IsZero (A i)) :
    IsZero B := by
  obtain ⟨χ, -, hu⟩ := h B (fun _ => 0) (fun _ => comp_zero)
  rw [IsZero.iff_id_eq_zero]
  exact (hu (𝟙 B) fun i => (hA i).eq_of_src _ _).trans
    (hu 0 fun i => (hA i).eq_of_src _ _).symm

end IsSystemColimit

section Existence

variable [HasCoproductsOfShape K 𝒞] [HasCoproductsOfShape (Σ i j : K, i ⟶ j) 𝒞]
  [HasCoequalizers 𝒞] (A : K → 𝒞) (T : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i))

/-- The first of the two maps whose coequalizer is the colimit of a system: on the summand of an
arrow `a : i ⟶ j` it is the transition map followed by the inclusion of `A i`. -/
noncomputable def systemColimitLeft : (∐ fun x : Σ i j : K, i ⟶ j => A x.2.1) ⟶ ∐ A :=
  Sigma.desc fun x => T x.2.2 ≫ Sigma.ι A x.1

/-- The second of the two maps whose coequalizer is the colimit of a system: on the summand of an
arrow `a : i ⟶ j` it is the inclusion of `A j`. -/
noncomputable def systemColimitRight : (∐ fun x : Σ i j : K, i ⟶ j => A x.2.1) ⟶ ∐ A :=
  Sigma.desc fun x => Sigma.ι A x.2.1

/-- **The colimit of a system**, as a coequalizer of two maps between coproducts. -/
noncomputable def systemColimit : 𝒞 :=
  coequalizer (systemColimitLeft A T) (systemColimitRight A)

/-- The legs of the colimit of a system. -/
noncomputable def systemColimitι (i : K) : A i ⟶ systemColimit A T :=
  Sigma.ι A i ≫ coequalizer.π _ _

/-- The legs of the colimit of a system are compatible with the transition maps. -/
theorem systemColimitι_compatible {i j : K} (a : i ⟶ j) :
    T a ≫ systemColimitι A T i = systemColimitι A T j := by
  have h := congrArg (Sigma.ι (fun x : Σ i j : K, i ⟶ j => A x.2.1) ⟨i, j, a⟩ ≫ ·)
    (coequalizer.condition (systemColimitLeft A T) (systemColimitRight A))
  simpa [systemColimitLeft, systemColimitRight, systemColimitι, systemColimit] using h

/-- **Colimits of systems exist** in a category with the relevant coproducts and coequalizers. -/
theorem isSystemColimit_systemColimit :
    IsSystemColimit A T (systemColimit A T) (systemColimitι A T) := by
  intro G τ hτ
  have hc : systemColimitLeft A T ≫ Sigma.desc τ = systemColimitRight A ≫ Sigma.desc τ := by
    refine Sigma.hom_ext _ _ fun x => ?_
    simp [systemColimitLeft, systemColimitRight, hτ]
  refine ⟨coequalizer.desc (Sigma.desc τ) hc, fun i => by
    simp [systemColimitι, systemColimit], fun χ hχ => ?_⟩
  refine coequalizer.hom_ext (Sigma.hom_ext _ _ fun i => ?_)
  simpa [systemColimitι, systemColimit] using (Category.assoc _ _ _).symm.trans (hχ i)

end Existence

section Iso

variable {I : Type w₁} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {A : Iᵒᵖ → 𝒞} {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (A j ⟶ A i)} {B : 𝒞} {ψ : ∀ i, A i ⟶ B}

/-- **A system whose legs are isomorphisms has its vertex as colimit.** Over a directed set, if
every leg `ψ i : A i ⟶ B` of a compatible family is an isomorphism, then `ψ` exhibits `B` as the
colimit of the system. -/
theorem IsSystemColimit.of_isIso (hψ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ψ i = ψ j)
    [∀ i, IsIso (ψ i)] : IsSystemColimit A T B ψ := by
  intro G τ hτ
  obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
  have key : ∀ i : Iᵒᵖ, inv (ψ i) ≫ τ i = inv (ψ (Opposite.op i₀)) ≫ τ (Opposite.op i₀) := by
    have step : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), inv (ψ j) ≫ τ j = inv (ψ i) ≫ τ i := by
      intro i j a
      have h : inv (ψ j) ≫ T a = inv (ψ i) := by
        rw [IsIso.inv_comp_eq, ← hψ a, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [← hτ a, ← Category.assoc, h]
    intro i
    obtain ⟨k, hik, hi₀k⟩ := directed_of (· ≤ ·) i.unop i₀
    exact (step (i := Opposite.op k) (j := i) (homOfLE hik).op).trans
      (step (i := Opposite.op k) (j := Opposite.op i₀) (homOfLE hi₀k).op).symm
  refine ⟨inv (ψ (Opposite.op i₀)) ≫ τ (Opposite.op i₀), fun i => ?_, fun χ hχ => ?_⟩
  · rw [← key i, IsIso.hom_inv_id_assoc]
  · rw [← hχ, IsIso.inv_hom_id_assoc]

end Iso

end CategoryTheory.Limits
