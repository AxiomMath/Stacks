module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Order.RelSeries

/-!
# Filtrations with prescribed quotients from a fibre functor with `ℓ`-group monodromy

Let `𝒜` be an abelian category, `K` an object of `𝒜` and `P` a property of objects of `𝒜` closed
under kernels and cokernels and satisfied by `K`, all of whose objects are killed by a prime `ℓ`.
Suppose given a fully faithful additive *fibre functor* `Θ` from the objects with `P` to abelian
groups with an action of a group `π`, such that:

* `Θ K` has `ℓ` elements and `π` acts trivially on it;
* every `Θ G` is finite and `Θ` carries epimorphisms to surjections.

Then every object `G` with `P` on whose image `π` acts through an `ℓ`-group — every element of
`π` has an `ℓ`-power acting trivially — has a finite filtration running from a zero subobject to
the whole of `G` whose successive quotients are all isomorphic to `K`.

This is the categorical core of the proof of Stacks Tag 0A3R: for a finite type locally constant
sheaf of `F_ℓ`-vector spaces on a connected scheme, `K` is the constant sheaf `Z/ℓ`, and `Θ` is
the geometric fibre at a geometric point, acted on by the étale fundamental group.

## Main definitions

* `CategoryTheory.Abelian.CokernelIsoStep K A`: the relation on subobjects of `A` of being
  contained in one another with quotient isomorphic to `K`.

## Main results

* `CategoryTheory.Abelian.cokernelIsoStep_pullback`: pulling subobjects back along an
  epimorphism preserves the relation.
* `CategoryTheory.Abelian.exists_relSeries_cokernelIsoStep`: the filtration described above.

## Implementation notes

The filtration is built by induction on the cardinality of the fibre. The number of fixed points
of an `ℓ`-group acting on a finite set is congruent to the cardinality of the set modulo `ℓ`, and
the fibre of a nonzero `G` is a nonzero `F_ℓ`-vector space, so besides `0` there is another fixed
point `x`. The group `Θ K` is cyclic of order `ℓ`; sending a generator to `x` is a morphism of
`π`-modules, which is `Θ s` for a morphism `s : K ⟶ G` by fullness, and `Θ s` is injective, so
`s` is a monomorphism. The fibre of the cokernel of `s` is a quotient of `Θ G` in which `x`
becomes `0`, so it is strictly smaller and the induction applies to it; its filtration is pulled
back to `G` and the subobject `s` is put at its bottom.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe w

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]

/-- One step of a filtration of `A` with quotient `K`: the first subobject is contained in the
second and the quotient of the second by the first is isomorphic to `K`. -/
def CokernelIsoStep (K A : 𝒜) : SetRel (Subobject A) (Subobject A) :=
  {p | ∃ h : p.1 ≤ p.2, Nonempty (cokernel (p.1.ofLE p.2 h) ≅ K)}

/-! ### Pulling a filtration back along an epimorphism -/

section Pullback

variable {G G' : 𝒜} (q : G ⟶ G') [Epi q]

/-- **Pulling back along an epimorphism preserves the quotient of two nested subobjects.** For
an epimorphism `q : G ⟶ G'` and subobjects `X ≤ Y` of `G'`, the induced morphism of the cokernel
of `q⁻¹X ⟶ q⁻¹Y` to the cokernel of `X ⟶ Y` is an isomorphism. -/
theorem isIso_cokernelMap_pullback {X Y : Subobject G'} (h : X ≤ Y) :
    IsIso (cokernel.map (((Subobject.pullback q).obj X).ofLE ((Subobject.pullback q).obj Y)
        ((Subobject.pullback q).monotone h)) (X.ofLE Y h)
      (Subobject.pullbackπ q X) (Subobject.pullbackπ q Y) (by
        rw [← cancel_mono Y.arrow, Category.assoc, Category.assoc,
          (Subobject.isPullback q Y).w, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow,
          (Subobject.isPullback q X).w])) := by
  generalize_proofs _ _ _ _ sq
  set a := ((Subobject.pullback q).obj X).ofLE ((Subobject.pullback q).obj Y)
    ((Subobject.pullback q).monotone h)
  set b := X.ofLE Y h
  set pX := Subobject.pullbackπ q X
  set pY := Subobject.pullbackπ q Y
  have hpb : IsPullback pX a b pY := by
    refine IsPullback.of_bot ?_ sq.symm (Subobject.isPullback q Y)
    simpa [a, b] using Subobject.isPullback q X
  set m := cokernel.map a b pX pY sq
  have hm : cokernel.π a ≫ m = pY ≫ cokernel.π b := by simp [m]
  have : Epi m := by
    have : Epi (cokernel.π a ≫ m) := by
      rw [hm]
      have : Epi pY := Abelian.epi_fst_of_isLimit _ _ (Subobject.isPullback q Y).isLimit
      exact epi_comp pY (cokernel.π b)
    exact epi_of_epi (cokernel.π a) m
  have : Mono m := by
    refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
    obtain ⟨A₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (cokernel.π a) g
    have hy0 : (y ≫ pY) ≫ cokernel.π b = 0 := by
      rw [Category.assoc, ← hm, ← Category.assoc, ← hy, Category.assoc, hg, comp_zero]
    have hS : (ShortComplex.mk b (cokernel.π b) (cokernel.condition b)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b)
    obtain ⟨A₂, π₂, _, x, hx⟩ := hS.exact_up_to_refinements (y ≫ pY) hy0
    have hz := hpb.lift_snd x (π₂ ≫ y) (by simpa using hx.symm)
    have h0 : (π₂ ≫ π₁) ≫ g = (π₂ ≫ π₁) ≫ 0 := by
      rw [Category.assoc, hy, ← Category.assoc, ← hz, Category.assoc,
        cokernel.condition, comp_zero, comp_zero]
    exact (cancel_epi (π₂ ≫ π₁)).1 h0
  exact isIso_of_mono_of_epi m

/-- **Pulling subobjects back along an epimorphism preserves the relation
`CokernelIsoStep`.** -/
theorem cokernelIsoStep_pullback {K : 𝒜} {X Y : Subobject G'}
    (hXY : (X, Y) ∈ CokernelIsoStep K G') :
    ((Subobject.pullback q).obj X, (Subobject.pullback q).obj Y) ∈ CokernelIsoStep K G := by
  obtain ⟨h, ⟨e⟩⟩ := hXY
  have := isIso_cokernelMap_pullback q h
  exact ⟨(Subobject.pullback q).monotone h, ⟨asIso (cokernel.map
    (((Subobject.pullback q).obj X).ofLE ((Subobject.pullback q).obj Y)
      ((Subobject.pullback q).monotone h)) (X.ofLE Y h)
    (Subobject.pullbackπ q X) (Subobject.pullbackπ q Y) _) ≪≫ e⟩⟩

/-- Pulling subobjects back along an epimorphism, as a morphism of relations. -/
noncomputable def cokernelIsoStepPullbackHom (K : 𝒜) :
    (CokernelIsoStep K G').Hom (CokernelIsoStep K G) where
  toFun := (Subobject.pullback q).obj
  map_rel' h := cokernelIsoStep_pullback q h

end Pullback

/-! ### The bottom step -/

section Bottom

variable {K G : 𝒜} (s : K ⟶ G) [Mono s]

/-- The preimage, under the cokernel of a monomorphism `s`, of a subobject with zero underlying
object is the subobject `s`. -/
theorem pullback_cokernel_π_eq_mk {Z : Subobject (cokernel s)} (hZ : IsZero (Z : 𝒜)) :
    (Subobject.pullback (cokernel.π s)).obj Z = Subobject.mk s := by
  have hk : IsLimit (KernelFork.ofι s (cokernel.condition s)) :=
    monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π s) (cokernel.condition s))
      (cokernelIsCokernel s)
  apply le_antisymm
  · refine Subobject.le_mk_of_comm
      (hk.lift (KernelFork.ofι ((Subobject.pullback (cokernel.π s)).obj Z).arrow ?_)) ?_
    · rw [← (Subobject.isPullback (cokernel.π s) Z).w, hZ.eq_of_tgt
        (Subobject.pullbackπ (cokernel.π s) Z) 0, zero_comp]
    · exact hk.fac _ WalkingParallelPair.zero
  · refine Subobject.mk_le_of_comm
      ((Subobject.isPullback (cokernel.π s) Z).lift 0 s (by simp)) ?_
    exact (Subobject.isPullback (cokernel.π s) Z).lift_snd _ _ _

/-- The zero subobject followed by the subobject `s` is a step with quotient `K`. -/
theorem bot_mk_mem_cokernelIsoStep : (⊥, Subobject.mk s) ∈ CokernelIsoStep K G := by
  have hz : (⊥ : Subobject G).ofLE (Subobject.mk s) bot_le = 0 :=
    (IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero).eq_of_src _ _
  exact ⟨bot_le, ⟨cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget ≪≫ Subobject.underlyingIso s⟩⟩

end Bottom

/-- If the inclusion of a subobject is an isomorphism, so is the inclusion of its preimage. -/
theorem isIso_pullback_arrow {G G' : 𝒜} (q : G ⟶ G') {Y : Subobject G'} [hY : IsIso Y.arrow] :
    IsIso ((Subobject.pullback q).obj Y).arrow :=
  (Subobject.isPullback q Y).isIso_snd_of_isIso


/-! ### The filtration -/

section Filtration

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (K : 𝒜) (P : ObjectProperty 𝒜) [P.IsClosedUnderKernels]
  [P.IsClosedUnderCokernels]
  (hK : P K) {π : Type*} [Group π] (Θ : P.FullSubcategory ⥤ Action AddCommGrpCat.{w} π)
  [Θ.Additive] [Θ.Full] [Θ.Faithful]
  (hK_card : Nat.card (Θ.obj ⟨K, hK⟩).V = ℓ)
  (hK_triv : ∀ (σ : π) (y : (Θ.obj ⟨K, hK⟩).V), ((Θ.obj ⟨K, hK⟩).ρ σ).asHom.hom y = y)
  (hfin : ∀ G : P.FullSubcategory, Finite (Θ.obj G).V)
  (hepi : ∀ {G H : P.FullSubcategory} (f : G ⟶ H), Epi f.hom →
    Function.Surjective (Θ.map f).hom)
  (htors : ∀ G : P.FullSubcategory, ℓ • 𝟙 G.obj = 0)

omit [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [Θ.Full] [Θ.Faithful] in
/-- The image of an object killed by `ℓ` is killed by `ℓ`, elementwise. -/
theorem nsmul_eq_zero_of_nsmul_id {G : P.FullSubcategory} (hG : ℓ • 𝟙 G.obj = 0)
    (x : (Θ.obj G).V) : ℓ • x = 0 := by
  have h0 : ℓ • 𝟙 G = 0 := by ext1; exact hG
  simpa [Functor.map_nsmul] using congrArg (fun f ↦ (Θ.map f).hom x) h0

include P in
omit [P.IsClosedUnderCokernels] [Θ.Full] in
/-- **A faithful functor preserving zero morphisms detects monomorphisms** when the objects with
`P` are closed under kernels: the kernel of a morphism with injective image maps to zero. -/
theorem mono_of_injective_map {G H : P.FullSubcategory} (f : G ⟶ H)
    (hf : Function.Injective (Θ.map f).hom) : Mono f.hom := by
  let k : (⟨kernel f.hom, P.prop_kernel f.hom G.property H.property⟩ : P.FullSubcategory) ⟶ G :=
    ObjectProperty.homMk (kernel.ι f.hom)
  have hk : k ≫ f = 0 := by
    ext1
    exact kernel.condition f.hom
  have hΘk : Θ.map k = 0 := by
    ext y
    apply hf
    have := congrArg (fun g ↦ (Θ.map g).hom y) hk
    simp only [Functor.map_comp, Action.comp_hom, Functor.map_zero, Action.zero_hom] at this
    simpa using this
  have hk0 : k = 0 := Θ.map_injective (by rw [hΘk, Functor.map_zero])
  exact Preadditive.mono_of_kernel_zero (congrArg InducedCategory.Hom.hom hk0)

omit [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [Θ.Full] in
/-- **A faithful functor preserving zero morphisms detects zero objects.** -/
theorem isZero_of_subsingleton {G : P.FullSubcategory} (hG : Subsingleton (Θ.obj G).V) :
    IsZero G.obj := by
  have h1 : 𝟙 (Θ.obj G) = 0 := by
    ext y
    exact Subsingleton.elim _ _
  have h2 : 𝟙 G = 0 := Θ.map_injective (by rw [Θ.map_id, h1, Functor.map_zero])
  exact (IsZero.iff_id_eq_zero _).2 (congrArg InducedCategory.Hom.hom h2)

/-- The action of `π` on a finite object, as an action on its underlying type. -/
abbrev actionMulAction (M : Action AddCommGrpCat.{w} π) : MulAction π M.V where
  smul σ x := (M.ρ σ).asHom.hom x
  one_smul x := by
    change (M.ρ 1).asHom.hom x = x
    simp
  mul_smul σ τ x := by
    change (M.ρ (σ * τ)).asHom.hom x = (M.ρ σ).asHom.hom ((M.ρ τ).asHom.hom x)
    simp

include hℓ hK_card hK_triv hfin hepi htors in
/-- **A filtration with quotients `K`, by induction on the size of the fibre.** -/
theorem exists_relSeries_cokernelIsoStep_aux (n : ℕ) :
    ∀ G : P.FullSubcategory, Nat.card (Θ.obj G).V = n →
      (∀ σ : π, ∃ k : ℕ, ∀ x : (Θ.obj G).V, ((Θ.obj G).ρ (σ ^ (ℓ ^ k))).asHom.hom x = x) →
      ∃ X : RelSeries (CokernelIsoStep K G.obj),
        IsZero (X.head : 𝒜) ∧ IsIso X.last.arrow := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hKfin : Finite (Θ.obj ⟨K, hK⟩).V := hfin _
  have : Nontrivial (Θ.obj ⟨K, hK⟩).V :=
    Finite.one_lt_card_iff_nontrivial.mp (hK_card ▸ hℓ.one_lt)
  obtain ⟨k₁, hk₁⟩ := exists_ne (0 : (Θ.obj ⟨K, hK⟩).V)
  have hgen : ∀ y : (Θ.obj ⟨K, hK⟩).V, y ∈ AddSubgroup.zmultiples k₁ :=
    fun y ↦ mem_zmultiples_of_prime_card hK_card hk₁
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hGn hmon
  set V := Θ.obj G
  have hVfin : Finite V.V := hfin G
  by_cases h1 : Subsingleton V.V
  · have hG := isZero_of_subsingleton P Θ h1
    refine ⟨RelSeries.singleton _ ⊤, ?_, ?_⟩
    · rw [RelSeries.head_singleton]
      exact IsZero.of_iso hG (asIso (⊤ : Subobject G.obj).arrow)
    · rw [RelSeries.last_singleton]
      infer_instance
  have hVℓ : ∀ x : V.V, ℓ • x = 0 := nsmul_eq_zero_of_nsmul_id P Θ (htors G)
  have hdvd : ℓ ∣ Nat.card V.V := by
    have hp : IsPGroup ℓ (Multiplicative V.V) := fun g ↦ ⟨1, by
      rw [pow_one]
      exact hVℓ (Multiplicative.toAdd g)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
    have hm' : Nat.card V.V = ℓ ^ m := hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm'
      exact h1 (Finite.card_le_one_iff_subsingleton.mp hm'.le)
    rw [hm']
    exact dvd_pow_self ℓ hm0
  let := actionMulAction V
  set Q := (MulAction.toPermHom π V.V).range
  have hQ : IsPGroup ℓ Q := by
    rintro ⟨g, σ, rfl⟩
    obtain ⟨k, hk⟩ := hmon σ
    refine ⟨k, Subtype.ext ?_⟩
    ext x
    change (MulAction.toPermHom π V.V σ ^ ℓ ^ k) x = x
    rw [← map_pow]
    exact hk x
  have : Finite Q := inferInstance
  have hfix : Nat.card V.V ≡ Nat.card (MulAction.fixedPoints Q V.V) [MOD ℓ] :=
    hQ.card_modEq_card_fixedPoints _
  have hzQ : (0 : V.V) ∈ MulAction.fixedPoints Q V.V := by
    rintro ⟨g, σ, rfl⟩
    change (V.ρ σ).asHom.hom 0 = 0
    exact map_zero _
  obtain ⟨x, hxQ, hx0⟩ : ∃ x ∈ MulAction.fixedPoints Q V.V, x ≠ 0 := by
    have hdvd' : ℓ ∣ Nat.card (MulAction.fixedPoints Q V.V) := by
      have hle : Nat.card (MulAction.fixedPoints Q V.V) ≤ Nat.card V.V :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
      have h3 := Nat.dvd_sub hdvd ((Nat.modEq_iff_dvd' hle).mp hfix.symm)
      rwa [Nat.sub_sub_self hle] at h3
    have hpos : 0 < Nat.card (MulAction.fixedPoints Q V.V) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, hzQ⟩⟩, inferInstance⟩
    have h2 : 1 < Nat.card (MulAction.fixedPoints Q V.V) :=
      lt_of_lt_of_le hℓ.one_lt (Nat.le_of_dvd hpos hdvd')
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ :=
      (Finite.one_lt_card_iff_nontrivial.mp h2).exists_pair_ne
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 ↦ hab (Subtype.ext (ha0.trans hb0.symm))⟩
    · exact ⟨a, ha, ha0⟩
  have hxfix : ∀ σ : π, (V.ρ σ).asHom.hom x = x := fun σ ↦ hxQ ⟨_, σ, rfl⟩
  let e := zmodAddEquivOfGenerator hgen hK_card
  let ψ₀ : ZMod ℓ →+ V.V := ZMod.lift ℓ ⟨zmultiplesHom V.V x, by
    simpa [zmultiplesHom_apply, natCast_zsmul] using hVℓ x⟩
  let ψ : (Θ.obj ⟨K, hK⟩).V →+ V.V := ψ₀.comp e.symm.toAddMonoidHom
  have hψgen : ∀ z : ℤ, ψ (z • k₁) = z • x := by
    intro z
    simp [ψ, ψ₀, e, zmodAddEquivOfGenerator_symm_apply_zsmul]
  have hψ : ∀ y, ∃ z : ℤ, y = z • k₁ ∧ ψ y = z • x := by
    intro y
    obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen y)
    exact ⟨z, rfl, hψgen z⟩
  let φ : Θ.obj ⟨K, hK⟩ ⟶ V :=
    { hom := AddCommGrpCat.ofHom ψ
      comm := fun σ ↦ by
        ext y
        obtain ⟨z, rfl, hz⟩ := hψ y
        change ψ (((Θ.obj ⟨K, hK⟩).ρ σ).asHom.hom (z • k₁)) = (V.ρ σ).asHom.hom (ψ (z • k₁))
        rw [hK_triv, hz, map_zsmul, hxfix] }
  obtain ⟨s', hs'⟩ := Θ.map_surjective φ
  set s : K ⟶ G.obj := s'.hom
  have hs'eq : s' = ObjectProperty.homMk s := rfl
  have hsk₁ : (Θ.map s').hom k₁ = x := by
    rw [hs']
    change ψ k₁ = x
    simpa using hψgen 1
  have hℓK : ∀ y : (Θ.obj ⟨K, hK⟩).V, ℓ • y = 0 :=
    nsmul_eq_zero_of_nsmul_id P Θ (htors ⟨K, hK⟩)
  have : Mono s := by
    refine mono_of_injective_map P Θ s' fun y₁ y₂ hy ↦ ?_
    obtain ⟨z₁, rfl, -⟩ := hψ y₁
    obtain ⟨z₂, rfl, -⟩ := hψ y₂
    rw [hs'] at hy
    change ψ (z₁ • k₁) = ψ (z₂ • k₁) at hy
    rw [hψgen, hψgen, ← sub_eq_zero, ← sub_smul] at hy
    rw [← sub_eq_zero, ← sub_smul]
    have hox : addOrderOf x = ℓ :=
      addOrderOf_eq_prime (hVℓ x) hx0
    have hok : addOrderOf k₁ = ℓ :=
      addOrderOf_eq_prime (hℓK k₁) hk₁
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero] at hy ⊢
    rwa [hok, ← hox]
  let G' : P.FullSubcategory := ⟨cokernel s, P.prop_cokernel s hK G.property⟩
  let q : G ⟶ G' := ObjectProperty.homMk (cokernel.π s)
  have hqsurj : Function.Surjective (Θ.map q).hom := hepi q (by dsimp [q]; infer_instance)
  have hqx : (Θ.map q).hom x = 0 := by
    have hsq : s' ≫ q = 0 := by
      ext1
      exact cokernel.condition s
    simpa [hsk₁] using congrArg (fun f ↦ (Θ.map f).hom k₁) hsq
  have hlt : Nat.card (Θ.obj G').V < n := by
    rw [← hGn]
    have := Fintype.ofFinite V.V
    have : Finite (Θ.obj G').V := hfin G'
    have := Fintype.ofFinite (Θ.obj G').V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective _ hqsurj fun hinj ↦ hx0 (hinj ?_)
    rw [hqx, map_zero]
  have hmon' : ∀ σ : π, ∃ k : ℕ, ∀ y : (Θ.obj G').V,
      ((Θ.obj G').ρ (σ ^ (ℓ ^ k))).asHom.hom y = y := by
    intro σ
    obtain ⟨k, hk⟩ := hmon σ
    refine ⟨k, fun y ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hqsurj y
    have hc := congrArg (fun f ↦ f y) ((Θ.map q).comm (σ ^ (ℓ ^ k)))
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at hc
    rw [hk y] at hc
    exact hc.symm
  obtain ⟨X', hX'head, hX'last⟩ := ih _ hlt G' rfl hmon'
  let Y := X'.map (cokernelIsoStepPullbackHom (cokernel.π s) K)
  have hYhead : Y.head = Subobject.mk s := pullback_cokernel_π_eq_mk s hX'head
  refine ⟨Y.cons ⊥ (hYhead ▸ bot_mk_mem_cokernelIsoStep s), ?_, ?_⟩
  · rw [RelSeries.head_cons]
    exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
  · rw [RelSeries.last_cons]
    exact isIso_pullback_arrow (cokernel.π s) (Y := X'.last)

include hℓ hK_card hK_triv hfin hepi htors in
/-- **A filtration with quotients `K` of an object with `ℓ`-group monodromy.** Let `Θ` be a fully
faithful additive functor from the objects with `P` (a property closed under cokernels) to
abelian groups with an action of `π`, taking finite values and carrying epimorphisms to
surjections, where `P` is also closed under kernels, and carrying `K` to a group of order `ℓ`
with trivial action; suppose every object with `P` is killed by the prime `ℓ`. Then an object
`G` with `P` on whose image every element of `π` has an `ℓ`-power acting trivially has a finite
filtration from a zero subobject to the whole of `G` with all successive quotients
isomorphic to `K`. -/
theorem exists_relSeries_cokernelIsoStep (G : P.FullSubcategory)
    (hmon : ∀ σ : π, ∃ k : ℕ, ∀ x : (Θ.obj G).V, ((Θ.obj G).ρ (σ ^ (ℓ ^ k))).asHom.hom x = x) :
    ∃ X : RelSeries (CokernelIsoStep K G.obj), IsZero (X.head : 𝒜) ∧ IsIso X.last.arrow :=
  exists_relSeries_cokernelIsoStep_aux hℓ K P hK Θ hK_card hK_triv hfin hepi htors _ G rfl hmon

end Filtration

end CategoryTheory.Abelian
