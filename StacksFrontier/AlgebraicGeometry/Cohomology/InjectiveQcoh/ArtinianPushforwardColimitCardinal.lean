module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ArtinianPushforwardColimit
public import StacksFrontier.AlgebraicGeometry.Size.Affine
import all StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ArtinianPushforwardColimit

/-!
# Injective quasi-coherent modules on a Noetherian affine scheme, with cardinality bounds

This file sharpens `AlgebraicGeometry.exists_filtered_colimit_pushforwards_artinian`, the
presentation of Stacks 09TI, in two ways that the transport of that presentation to other sites
needs.

* Each term of the diagram is exhibited as the direct image of the module `Ñ` associated with a
  finite module `N` over the Artinian ring `R`, rather than of an abstract coherent module.
* The Artinian rings are bounded in size by the ring of global sections `A` of the base:
  `#R ≤ max ℵ₀ #A`.  The bound is what places their spectra in any big site that contains the
  base scheme.

The construction is the same as in the source.  An indecomposable injective `A`-module `E` is
exhausted by submodules that are finite over the quotients `A_𝔭 / 𝔪^(n+1)`, so
`#E ≤ max ℵ₀ #A`.  Hence each stage of the filtered presentation, which is a finite direct sum of
submodules of such `E`, has cardinality at most `max ℵ₀ #A`.  A finite module `N` over an Artinian
ring `B` is still a finite module over the Artinian quotient `B / Ann_B(N)`, and that quotient
embeds into a finite power of `N`, so its cardinality is bounded by that of `N`.

## Main results

* `AlgebraicGeometry.exists_filtered_colimit_tilde_pushforwards_artinian_card_le`: Stacks 09TI
  with associated-module terms and bounded Artinian rings.

## References

* [Stacks Project, Tag 09TI](https://stacks.math.columbia.edu/tag/09TI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- A type of cardinality at most that of a finite power of `Y` has cardinality at most
`max ℵ₀ #Y`. -/
private theorem mk_le_max_aleph0_of_le_mk_fin_pi {X Y : Type u} (k : ℕ)
    (h : #X ≤ #(Fin k → Y)) : #X ≤ max ℵ₀ #Y :=
  calc #X ≤ #(Fin k → Y) := h
    _ = #Y ^ k := by simp
    _ ≤ (max ℵ₀ #Y) ^ k := power_le_power_right (le_max_right _ _)
    _ ≤ max ℵ₀ #Y := power_nat_le (le_max_left _ _)

/-- A finite module over a ring `B` has cardinality at most `max ℵ₀ #B`: it is a quotient of a
finite power of `B`. -/
theorem mk_le_max_aleph0_of_finite (B : Type u) [CommRing B] (M : Type u) [AddCommGroup M]
    [Module B M] [Module.Finite B M] : #M ≤ max ℵ₀ #B := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := M)
  have hsurj : Function.Surjective (Fintype.linearCombination B s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  exact mk_le_max_aleph0_of_le_mk_fin_pi k (mk_le_of_surjective hsurj)

/-- An indecomposable injective module over a Noetherian ring `R` has cardinality at most
`max ℵ₀ #R`.  It is the union of the submodules killed by the powers of the maximal ideal of
`R_𝔭`, each of which is finite over a quotient of `R_𝔭`. -/
theorem mk_le_max_aleph0_of_indecomposable_injective (R : Type u) [CommRing R]
    [IsNoetherianRing R] (E : ModuleCat.{u} R) [Injective E] (hE : Indecomposable E) :
    #E ≤ max ℵ₀ #R := by
  obtain ⟨p, hp, ms, tower, j, hj, -, hfin, hex⟩ :=
    indecomposable_injective_has_artinian_stages R E hE
  let A := Localization.AtPrime p
  let Q (n : ℕ) := Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n
  have hA : #A ≤ max ℵ₀ #R := mk_le_of_isLocalization p.primeCompl A
  have hQ (n : ℕ) : #(Q n) ≤ max ℵ₀ #R := by
    have := hfin n
    exact (mk_le_max_aleph0_of_finite (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) (Q n)).trans
      (max_le (le_max_left _ _) ((mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hA))
  have hmono : Monotone Q := fun n m hnm x hx ↦
    (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦ ((Submodule.mem_torsionBySet_iff _ _).mp hx)
      ⟨a.val, Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1) a.property⟩
  have hsurj : Function.Surjective (fun x : (n : ℕ) × Q n => (x.2 : E)) := by
    intro x
    have hx : x ∈ (⨆ n, Q n) := hex ▸ Submodule.mem_top
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed Q hmono.directed_le).mp hx
    exact ⟨⟨n, ⟨x, hn⟩⟩, rfl⟩
  calc #E ≤ #((n : ℕ) × Q n) := mk_le_of_surjective hsurj
    _ = sum fun n => #(Q n) := mk_sigma _
    _ ≤ #(ULift.{u} ℕ) * ⨆ n, #(Q n) := by
        rw [mk_uLift]
        simpa using sum_le_lift_mk_mul_iSup (fun n => #(Q n))
    _ ≤ max ℵ₀ #R * max ℵ₀ #R :=
        mul_le_mul' (by simp) (ciSup_le' hQ)
    _ = max ℵ₀ #R := mul_eq_self (le_max_left _ _)

/-- A finite module `N` over an Artinian ring `B` restricts, along any `φ : R →+* B`, to the
restriction of a finite module over an Artinian ring of cardinality at most `max ℵ₀ #N`: the
quotient `B / Ann_B(N)`, which embeds into a finite power of `N`. -/
theorem exists_artinian_restrictScalars_card_le {R : Type u} [CommRing R]
    (B : CommRingCat.{u}) [IsArtinianRing B] (φ : R →+* B) (N : ModuleCat.{u} B)
    [Module.Finite B N] :
    ∃ (B' : CommRingCat.{u}) (φ' : R →+* B') (N' : ModuleCat.{u} B'),
      IsArtinianRing B' ∧ Module.Finite B' N' ∧ #B' ≤ max ℵ₀ #N ∧
        Nonempty ((ModuleCat.restrictScalars φ).obj N ≅
          (ModuleCat.restrictScalars φ').obj N') := by
  let I := Module.annihilator B N
  let : Module (B ⧸ I) N := Module.quotientAnnihilator
  have htor := Module.isTorsionBySet_annihilator B N
  let : IsScalarTower B (B ⧸ I) N := .of_algebraMap_smul fun b x => htor.mk_smul b x
  let B' := CommRingCat.of (B ⧸ I)
  let N' : ModuleCat.{u} B' := ModuleCat.of (B ⧸ I) N
  have hfin : Module.Finite B' N' :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ I) N
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  have hinj : Function.Injective (fun b : B ⧸ I => fun i : Fin k => b • s i) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, Module.mem_annihilator]
    intro x
    have hx : x ∈ Submodule.span B (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        have h : a • s i = b • s i :=
          (htor.mk_smul a (s i)).symm.trans ((congrFun hab i).trans (htor.mk_smul b (s i)))
        rw [sub_smul, h, sub_self]
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  let e : (ModuleCat.restrictScalars φ).obj N ≃ₗ[R]
      (ModuleCat.restrictScalars ((Ideal.Quotient.mk I).comp φ : R →+* B')).obj N' :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (htor.mk_smul (φ r) x).symm }
  refine ⟨B', (Ideal.Quotient.mk I).comp φ, N', inferInstanceAs (IsArtinianRing (B ⧸ I)), hfin,
    ?_, ⟨LinearEquiv.toModuleIso e⟩⟩
  exact mk_le_max_aleph0_of_le_mk_fin_pi k (mk_le_of_injective hinj)

/-- An injective module `J` over a Noetherian ring `R` is a filtered colimit of modules of
cardinality at most `max ℵ₀ #R`, each of which is the restriction of a finite module over an
Artinian ring of cardinality at most `max ℵ₀ #R`. -/
theorem injective_module_colimit_card_le (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : ModuleCat.{u} R) [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I), letI := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ ModuleCat.{u} R) (c : Cocone D),
        Nonempty (c.pt ≅ J) ∧ Nonempty (IsColimit c) ∧
        ∀ i, ∃ (B : CommRingCat.{u}) (φ : R →+* B) (N : ModuleCat.{u} B),
          IsArtinianRing B ∧ Module.Finite B N ∧ #B ≤ max ℵ₀ #R ∧
            Nonempty (D.obj i ≅ (ModuleCat.restrictScalars φ).obj N) := by
  classical
  obtain ⟨α, E, e, hinj, hind⟩ := Module.exists_iso_directSum_of_injective R J
  let (a : α) := hinj a
  choose P hmono hex hstage using fun a => indecomposable_filtration R (E a) (hind a)
  let T := StageIndex α
  let : DecidableEq T := Classical.decEq _
  let G (i : T) : Type u := ArtinianStageSubmodule (fun a => E a) P i
  let f : ∀ i j : T, i ≤ j → G i →ₗ[R] G j :=
    fun i j h => Submodule.inclusion
      (artinianStageSubmodule_mono (fun a => E a) P (fun a _ _ h => hmono a h) i j h)
  let : DirectedSystem G (fun {i j} h => f i j h) :=
    ⟨fun _ _ => Subtype.ext rfl, fun _ _ _ _ _ _ => Subtype.ext rfl⟩
  let eL := (filteredStageDirectSumEquiv (fun a => E a) P
    (fun a _ _ h => hmono a h) hex).some
  let : SmallCategory T := Preorder.smallCategory T
  refine ⟨T, Preorder.smallCategory T, inferInstance, ModuleCat.directLimitDiagram G f,
    ModuleCat.directLimitCocone G f, ⟨eL.toModuleIso ≪≫ e.symm⟩,
    ⟨ModuleCat.directLimitIsColimit G f⟩, ?_⟩
  intro i
  obtain ⟨B, φ, N, hB, hN, ⟨eN⟩⟩ := finite_sum_restrictScalars R
    (fun a : {a // a ∈ (i.1 : Set α)} => ModuleCat.of R (P a.val (i.2 a.val)))
    (fun a => hstage a.val (i.2 a.val))
  let eG := LinearEquiv.ofInjective (artinianStageToTotal (fun a => E a) P i)
    (artinianStageToTotal_injective (fun a => E a) P i)
  have hG : #(G i) ≤ max ℵ₀ #R := by
    let ι := {a // a ∈ (i.1 : Set α)}
    let X : ι → Type u := fun a => P a.1 (i.2 a.1)
    calc #(G i) = #(ArtinianStage R α (fun a => E a) P i) := (Cardinal.mk_congr eG.toEquiv).symm
      _ = #((a : ι) → X a) :=
          Cardinal.mk_congr (DirectSum.linearEquivFunOnFintype R ι X).toEquiv
      _ = ∏ a : ι, #(X a) := by rw [mk_pi, prod_eq_of_fintype, lift_id]
      _ ≤ max ℵ₀ #R := prod_le_of_le_of_aleph0_le Finset.univ _ _ (le_max_left _ _)
          fun a _ => (mk_le_mk_of_subset (Set.subset_univ _)).trans
            ((Cardinal.mk_set_le _).trans (by
              simpa using mk_le_max_aleph0_of_indecomposable_injective R (E a.1) (hind a.1)))
  have hN' : #N ≤ max ℵ₀ #R :=
    (Cardinal.mk_congr (eG.symm.toModuleIso ≪≫ eN).toLinearEquiv.toEquiv).symm.le.trans hG
  obtain ⟨B', φ', N', hB', hN'', hcard, ⟨e'⟩⟩ :=
    exists_artinian_restrictScalars_card_le B φ N
  exact ⟨B', φ', N', hB', hN'', hcard.trans (max_le (le_max_left _ _) hN'),
    ⟨eG.symm.toModuleIso ≪≫ eN ≪≫ e'⟩⟩

/-- **Stacks 09TI, with bounded Artinian rings.**  An injective quasi-coherent module `J` on a
Noetherian affine scheme `S` is a filtered colimit of direct images `(Spec R ⟶ S)_* Ñ` of the
modules associated with finite modules `N` over Artinian rings `R`, and the rings can be chosen of
cardinality at most `max ℵ₀ #Γ(S, ⊤)`.

This is `AlgebraicGeometry.exists_filtered_colimit_pushforwards_artinian` with the coherent
modules written as `Ñ` and with the bound added; the construction is the same. -/
theorem exists_filtered_colimit_tilde_pushforwards_artinian_card_le
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (J : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    [Injective J] :
    ∃ (I : Type u) (inst : SmallCategory I),
      letI := inst
      ∃ (_ : IsFiltered I)
        (D : I ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
        (φ : D ⟶ (Functor.const I).obj J),
        (∀ i, ∃ (R : CommRingCat.{u}) (_ : IsArtinianRing R) (f : Spec R ⟶ S)
            (N : ModuleCat.{u} R), Module.Finite R N ∧ #R ≤ max ℵ₀ #Γ(S, ⊤) ∧
              Nonempty ((D.obj i).obj ≅ (Scheme.Modules.pushforward f).obj (tilde N))) ∧
          Nonempty (IsColimit (Cocone.mk J φ)) := by
  classical
  let R := Γ(S, ⊤)
  let eS : Spec R ≅ S := S.isoSpec.symm
  let e := (tildeEquiv (R := R)).trans (quasicoherentPushforwardIso eS)
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let M := e.inverse.obj J
  have : Injective M := e.inverse.injective_obj J
  obtain ⟨I, inst, hf, D, c, ⟨ec⟩, ⟨hc⟩, hD⟩ := injective_module_colimit_card_le R M
  let c' := e.functor.mapCocone c
  let ec' : c'.pt ≅ J := e.functor.mapIso ec ≪≫ e.counitIso.app J
  let c'' := c'.extend ec'.hom
  refine ⟨I, inst, hf, D ⋙ e.functor, c''.ι, ?_, ?_⟩
  · intro i
    obtain ⟨B, ψ, N, hB, hN, hcard, ⟨eN⟩⟩ := hD i
    let φ : R ⟶ B := CommRingCat.ofHom ψ
    refine ⟨B, hB, Spec.map φ ≫ eS.hom, N, hN, hcard, ?_⟩
    let h := (tilde.functor R).mapIso eN ≪≫
      ((pushforwardTildeIso R B φ).app N).symm
    exact ⟨(Scheme.Modules.pushforward eS.hom).mapIso h ≪≫
      (Scheme.Modules.pushforwardComp (Spec.map φ) eS.hom).app (tilde N)⟩
  · exact ⟨(isColimitOfPreserves e.functor hc).ofIsoColimit (c'.extendIso ec')⟩

end AlgebraicGeometry

end
