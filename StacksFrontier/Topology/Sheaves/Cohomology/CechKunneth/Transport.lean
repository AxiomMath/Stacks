module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Complex

/-!
# Comparing Čech cohomology along maps of cochains and of lattices

Let `P` and `P'` be presheaves of `k`-modules on complete lattices, with families `U` and `U'`.
A family of `k`-linear maps of Čech cochains commuting with the Čech differentials induces a map
`Ȟ^p(U, P) ⟶ Ȟ^p(U', P')`, bijective when the maps of cochains are. Two instances are used in the
proof of the Künneth formula [Stacks, Tag 0BED]:

* a morphism of presheaves `P ⟶ P'` bijective on the members of the nerve of `U`
  (`Stacks.CechKunneth.bijective_Hmap_of_bijective`), and
* a monotone map `m : L ⟶ L'` of lattices carrying the nerve of `U` to the nerve of `m ∘ U`, along
  which `Ȟ^p(U, m^* R) ≅ Ȟ^p(m ∘ U, R)` (`Stacks.CechKunneth.transportEquiv`).

## Main definitions

* `Stacks.CechKunneth.HmapOf`: the map on Čech cohomology induced by maps of cochains.
* `Stacks.CechKunneth.transportEquiv`: the comparison along a map of lattices.
* `Stacks.CechKunneth.refCochain`: the refinement map of Čech cochains ([Stacks, Tag 01FD]).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.CechKunneth

variable {k : Type u} [CommRing k] {L L' : Type u} [CompleteLattice L] [CompleteLattice L']
  {ι ι' : Type u}

section HmapOf

variable {P : Lᵒᵖ ⥤ ModuleCat.{u} k} {P' : L'ᵒᵖ ⥤ ModuleCat.{u} k} {U : ι → L} {U' : ι' → L'}
  (φ : ∀ p, Cochain P U p →ₗ[k] Cochain P' U' p)
  (hφ : ∀ p c, d P' U' p (φ p c) = φ (p + 1) (d P U p c))

/-- **The map on Čech cohomology induced by maps of cochains commuting with the differentials.** -/
def HmapOf (p : ℕ) : H P U p →ₗ[k] H P' U' p :=
  Submodule.mapQ _ _ ((φ p).restrict fun z (hz : d P U p z = 0) => by
      change d P' U' p _ = 0
      rw [hφ, hz, map_zero]) (by
    cases p with
    | zero =>
      intro z hz
      simp only [coboundaries, Submodule.mem_bot] at hz
      subst hz
      exact Submodule.zero_mem _
    | succ p =>
      rintro ⟨z, hz⟩ ⟨w, rfl⟩
      exact ⟨φ p w, hφ p w⟩)

/-- `HmapOf` sends the class of a cocycle `z` to the class of `φ p z`. -/
theorem HmapOf_Hmk {p : ℕ} (z : Cochain P U p) (hz : d P U p z = 0) :
    HmapOf φ hφ p (Hmk P U z hz) = Hmk P' U' (φ p z) (by rw [hφ, hz, map_zero]) :=
  rfl

/-- **Bijective maps of cochains induce bijections on Čech cohomology.** -/
theorem bijective_HmapOf (hb : ∀ p, Function.Bijective (φ p)) (p : ℕ) :
    Function.Bijective (HmapOf φ hφ p) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
    rw [HmapOf_Hmk] at hx
    cases p with
    | zero =>
      rw [Hmk_eq_zero_iff_zero] at hx ⊢
      exact (hb 0).1 (hx.trans (map_zero _).symm)
    | succ q =>
      rw [Hmk_eq_zero_iff_succ] at hx ⊢
      obtain ⟨w', hw'⟩ := hx
      obtain ⟨w, rfl⟩ := (hb q).2 w'
      exact ⟨w, (hb (q + 1)).1 ((hφ q w).symm.trans hw')⟩
  · obtain ⟨z', hz', rfl⟩ := Hmk_surjective P' U' x
    obtain ⟨z, rfl⟩ := (hb p).2 z'
    have hz : d P U p z = 0 := (hb (p + 1)).1 (by rw [← hφ, hz', map_zero])
    exact ⟨Hmk P U z hz, rfl⟩

end HmapOf

/-- **A morphism of presheaves bijective on the nerve induces bijections on Čech cohomology.** -/
theorem bijective_Hmap_of_bijective {P P' : Lᵒᵖ ⥤ ModuleCat.{u} k} (U : ι → L) (f : P ⟶ P')
    (hf : ∀ {p : ℕ} (s : Fin (p + 1) → ι), Function.Bijective (f.app (op (inter U s))).hom)
    (p : ℕ) : Function.Bijective (Hmap U f p) :=
  bijective_HmapOf (mapCochain U f) (fun p c => (mapCochain_d U f p c).symm)
    (fun _ => ⟨fun _ _ h => funext fun s => (hf s).1 (congrFun h s),
      fun c' => ⟨fun s => ((hf s).2 (c' s)).choose,
        funext fun s => ((hf s).2 (c' s)).choose_spec⟩⟩) p

/-! ### Transport along a map of lattices -/

section Transport

variable (m : L ⥤ L') (R : L'ᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L)
  (hm : ∀ {p : ℕ} (s : Fin (p + 1) → ι), m.obj (inter U s) = inter (m.obj ∘ U) s)

/-- Restriction in `m^* R` along `Z ≤ Z'` is restriction in `R` along `m Z ≤ m Z'`. -/
theorem res_comp {Z Z' : L} (h : Z ≤ Z') (x : (m.op ⋙ R).obj (op Z')) :
    res (m.op ⋙ R) h x = res R (leOfHom (m.map (homOfLE h))) x :=
  rfl

/-- The cochains of `m^* R` for `U` as cochains of `R` for `m ∘ U`. -/
def transportCochain (p : ℕ) : Cochain (m.op ⋙ R) U p →ₗ[k] Cochain R (m.obj ∘ U) p where
  toFun c s := res R (hm s).ge (c s)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

/-- The cochains of `R` for `m ∘ U` as cochains of `m^* R` for `U`. -/
def transportCochainInv (p : ℕ) : Cochain R (m.obj ∘ U) p →ₗ[k] Cochain (m.op ⋙ R) U p where
  toFun c s := res R (hm s).le (c s)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

/-- `transportCochain` commutes with the Čech differentials. -/
theorem transportCochain_d (p : ℕ) (c : Cochain (m.op ⋙ R) U p) :
    d R (m.obj ∘ U) p (transportCochain m R U hm p c) =
      transportCochain m R U hm (p + 1) (d (m.op ⋙ R) U p c) := by
  funext s
  show _ = res R _ (∑ j : Fin (p + 2), _)
  rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, res_comp]
  show _ • res R _ (res R _ (c _)) = _ • res R _ (res R _ (c _))
  rw [res_res, res_res]

/-- **Čech cohomology of `m^* R` for `U` is Čech cohomology of `R` for `m ∘ U`**, when `m` carries
the nerve of `U` to the nerve of `m ∘ U`. -/
def transportEquiv (p : ℕ) : H (m.op ⋙ R) U p ≃ₗ[k] H R (m.obj ∘ U) p :=
  LinearEquiv.ofBijective (HmapOf (transportCochain m R U hm) (transportCochain_d m R U hm) p)
    (bijective_HmapOf _ _ (fun p => ⟨fun c c' h => funext fun s => by
        have := congrArg (res R (hm s).le) (congrFun h s)
        change res R _ (res R _ (c s)) = res R _ (res R _ (c' s)) at this
        rwa [res_res, res_res, res_self, res_self] at this,
      fun c => ⟨transportCochainInv m R U hm p c, funext fun s => by
        change res R _ (res R _ (c s)) = c s
        rw [res_res, res_self]⟩⟩) p)

/-- `transportEquiv` sends the class of a cocycle `z` to the class of its image under
`transportCochain`. -/
theorem transportEquiv_Hmk {p : ℕ} (z : Cochain (m.op ⋙ R) U p) (hz : d (m.op ⋙ R) U p z = 0) :
    transportEquiv m R U hm p (Hmk _ U z hz) =
      Hmk R (m.obj ∘ U) (transportCochain m R U hm p z)
        (by rw [transportCochain_d, hz, map_zero]) :=
  rfl

end Transport

/-! ### Refinement -/

section Refinement

variable (P : Lᵒᵖ ⥤ ModuleCat.{u} k) {ι'' : Type u} (U : ι → L) (U' : ι'' → L) (r : ι'' → ι)
  (hr : ∀ j, U' j ≤ U (r j))

include hr in
/-- If `U'_j ≤ U_{r j}` for every `j`, the intersection of `U'` along `s` lies below the
intersection of `U` along `r ∘ s`. -/
theorem inter_le_inter_refine {p : ℕ} (s : Fin (p + 1) → ι'') : inter U' s ≤ inter U (r ∘ s) :=
  iInf_mono fun j => hr (s j)

/-- **The refinement map of Čech cochains** ([Stacks, Tag 01FD]) along `r` with `U'_j ⊆ U_{r j}`:
`(ρ c)_s = c_{r ∘ s}|`. -/
def refCochain (p : ℕ) : Cochain P U p →ₗ[k] Cochain P U' p where
  toFun c s := res P (inter_le_inter_refine U U' r hr s) (c (r ∘ s))
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

/-- The value of the refinement of `c` at `s` is the restriction of `c (r ∘ s)`. -/
theorem refCochain_apply {p : ℕ} (c : Cochain P U p) (s : Fin (p + 1) → ι'') :
    refCochain P U U' r hr p c s = res P (inter_le_inter_refine U U' r hr s) (c (r ∘ s)) :=
  rfl

/-- The refinement map commutes with the Čech differentials. -/
theorem refCochain_d (p : ℕ) (c : Cochain P U p) :
    d P U' p (refCochain P U U' r hr p c) = refCochain P U U' r hr (p + 1) (d P U p c) := by
  funext s
  rw [refCochain_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, refCochain_apply, res_res, res_res]
  rfl

end Refinement

end Stacks.CechKunneth

end
