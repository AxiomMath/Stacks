module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import Mathlib.CategoryTheory.Galois.EssSurj
public import StacksFrontier.CategoryTheory.Galois.GaloisOfNormalStabilizer

/-!
# The connected cover attached to a proper open normal subgroup of `π₁`

Let `X` be a connected scheme with a geometric point `base` and `U` an open normal subgroup of
`π₁(X, base)` with `U ≠ π₁(X, base)`. Then there is a connected finite étale cover `Z` of `X` on
whose fibre at `base` every element of `U` acts trivially, and whose fibre has at least two points.

## Main results

* `AlgebraicGeometry.exists_connected_cover_of_isOpen_normal`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] {base : GeometricPoint X}

/-- The action of an element of the étale fundamental group on a fibre is the action of the
corresponding automorphism of the `FintypeCat`-valued fibre functor. -/
theorem autMulEquivEtaleFundamentalGroup_app_apply
    (σ : Aut (finiteEtaleFiberFintypeFunctor X base)) (A : FiniteEtaleOver X)
    (z : (finiteEtaleFiberFintypeFunctor X base).obj A) :
    (((autMulEquivEtaleFundamentalGroup X base) σ).app A).hom z = σ • z :=
  rfl

/-- **The connected cover attached to a proper open normal subgroup of `π₁`.** For an open
normal subgroup `U ≠ ⊤` of `π₁(X, base)` there is a connected finite étale cover `Z` of `X` with
at least two points in its fibre at `base`, on which every element of `U` acts trivially. -/
theorem exists_connected_cover_of_isOpen_normal (U : Subgroup (EtaleFundamentalGroup X base))
    (hUn : U.Normal) (hUo : IsOpen (U : Set (EtaleFundamentalGroup X base))) (hne : U ≠ ⊤) :
    ∃ Z : FiniteEtaleOver X, ConnectedSpace Z.left ∧ PreGaloisCategory.IsGalois Z ∧
      (∀ u ∈ U, ∀ z : (finiteEtaleFiberFunctor base).obj Z, (u.app Z).hom z = z) ∧
      2 ≤ Nat.card ((finiteEtaleFiberFunctor base).obj Z) := by
  set F := finiteEtaleFiberFintypeFunctor X base
  set e := autMulEquivEtaleFundamentalGroup X base
  set F' : FiniteEtaleOver X ⥤ FintypeCat.{u + 1} := F ⋙ FintypeCat.uSwitch.{u, u + 1}
  have : FiberFunctor F' := FiberFunctor.comp_right _
  set φ : Aut F ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{u, u + 1}).fullyFaithfulFunctor
  set V : Subgroup (Aut F') := U.comap (e.toMonoidHom.comp φ.symm.toMonoidHom)
  have hVn : V.Normal := hUn.comap _
  have hVo : IsOpen (V : Set (Aut F')) :=
    hUo.preimage ((continuous_autMulEquivEtaleFundamentalGroup X base).comp φ.symm.continuous)
  have hmem : ∀ σ : Aut F, φ σ ∈ V ↔ e σ ∈ U := fun σ => by
    show e (φ.symm (φ σ)) ∈ U ↔ _
    rw [ContinuousMulEquiv.symm_apply_apply]
  have hVne : V ≠ ⊤ := by
    intro hV
    apply hne
    rw [eq_top_iff]
    intro g _
    have h1 : φ (e.symm g) ∈ V := hV ▸ Subgroup.mem_top _
    simpa using (hmem _).1 h1
  have hconj : ∀ a ∈ V, ∀ b : Aut F', b⁻¹ * a * b ∈ V := fun a ha b => by
    simpa [mul_assoc] using hVn.conj_mem _ ha b⁻¹
  let W : OpenSubgroup (Aut F') := ⟨V, hVo⟩
  obtain ⟨A, ⟨iso⟩⟩ := exists_lift_of_quotient_openSubgroup (F := F') W
  set ψ : F'.obj A ≃ F.obj A := (F.obj A).uSwitchEquiv
  have hψ : ∀ (σ : Aut F) (y : F'.obj A), ψ (φ σ • y) = σ • ψ y := fun σ y =>
    (FintypeCat.uSwitchEquiv_naturality (σ.hom.app A) y).symm
  have hiso_inv : ∀ (σ : Aut F') (q : Aut F' ⧸ V), iso.inv.hom (σ • q) = σ • iso.inv.hom q :=
    fun σ q => congrArg (fun φ => φ q) (iso.inv.comm σ)
  have hiso_hom : ∀ y : F'.obj A, iso.inv.hom (iso.hom.hom y) = y := fun y =>
    congrArg (fun φ => φ y) (congrArg Action.Hom.hom iso.hom_inv_id)
  have hiso_hom' : ∀ q : Aut F' ⧸ V, iso.hom.hom (iso.inv.hom q) = q := fun q =>
    congrArg (fun φ => φ q) (congrArg Action.Hom.hom iso.inv_hom_id)
  have hquot : ∀ σ ∈ V, ∀ q : Aut F' ⧸ V, σ • q = q := by
    intro σ hσ q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    show (QuotientGroup.mk (σ * g) : Aut F' ⧸ V) = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hconj _ (V.inv_mem hσ) g
  have htrivA : ∀ σ ∈ V, ∀ y : F'.obj A, σ • y = y := by
    intro σ hσ y
    have h1 : σ • iso.inv.hom (iso.hom.hom y) = iso.inv.hom (iso.hom.hom y) :=
      (hiso_inv σ (iso.hom.hom y)).symm.trans (congrArg _ (hquot σ hσ _))
    exact (congrArg (σ • ·) (hiso_hom y).symm).trans (h1.trans (hiso_hom y))
  set a₀ : F.obj A := ψ (iso.inv.hom (QuotientGroup.mk 1))
  have htrans : ∀ y : F.obj A, ∃ σ : Aut F, σ • a₀ = y := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (iso.hom.hom (ψ.symm y))
    refine ⟨φ.symm g, ?_⟩
    have h1 : φ.symm g • a₀ = ψ (φ (φ.symm g) • iso.inv.hom (QuotientGroup.mk 1)) :=
      (hψ _ _).symm
    have h2 : φ (φ.symm g) • iso.inv.hom (QuotientGroup.mk 1 : Aut F' ⧸ V) =
        iso.inv.hom (QuotientGroup.mk g) := by
      rw [φ.apply_symm_apply]
      exact (hiso_inv g _).symm.trans (congrArg _ (by
        show (QuotientGroup.mk (g * 1) : Aut F' ⧸ V) = QuotientGroup.mk g
        rw [mul_one]))
    rw [h1, h2, hg]
    exact (congrArg ψ (hiso_hom (ψ.symm y))).trans (ψ.apply_symm_apply y)
  have htrivF : ∀ σ : Aut F, φ σ ∈ V → ∀ y : F.obj A, σ • y = y := by
    intro σ hσ y
    have h1 := hψ σ (ψ.symm y)
    rw [htrivA _ hσ, ψ.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨Z, i, z, hz, hconn, hmono⟩ := fiber_in_connected_component F A a₀
  have hinj : Function.Injective (F.map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback (F.map i)).1 inferInstance
  have hequiv : ∀ (σ : Aut F) (w : F.obj Z), F.map i (σ • w) = σ • F.map i w := fun σ w =>
    (congrArg (fun φ => φ w) (σ.hom.naturality i)).symm
  have hstabA : ∀ g : Aut F, g • a₀ = a₀ → φ g ∈ V := by
    intro g hg
    have h1 : ψ (iso.inv.hom (φ g • (QuotientGroup.mk 1 : Aut F' ⧸ V))) =
        ψ (iso.inv.hom (QuotientGroup.mk 1)) :=
      (congrArg ψ (hiso_inv (φ g) _)).trans ((hψ g _).trans hg)
    have h2 := congrArg iso.hom.hom (ψ.injective h1)
    rw [hiso_hom', hiso_hom'] at h2
    change (QuotientGroup.mk (φ g * 1) : Aut F' ⧸ V) = QuotientGroup.mk 1 at h2
    rw [QuotientGroup.eq, mul_one] at h2
    simpa using h2
  have hgal : PreGaloisCategory.IsGalois Z := by
    have := hconn
    refine PreGaloisCategory.isGalois_of_stabilizer_conj_mem F Z z (fun y => ?_) ?_
    · obtain ⟨σ, hσ⟩ := htrans (F.map i y)
      exact ⟨σ, hinj (by rw [hequiv, hz, hσ])⟩
    · intro g h hg
      have hga : g • a₀ = a₀ := by rw [← hz, ← hequiv, hg]
      have hV := hstabA g hga
      have hconj : φ (h⁻¹ * g * h) ∈ V := by
        rw [map_mul, map_mul, map_inv]
        exact hconj _ hV _
      exact hinj (by rw [hequiv, hz]; exact htrivF _ hconj _)
  refine ⟨Z, connectedSpace_left_of_isConnected Z hconn, hgal, ?_, ?_⟩
  · intro u hu w
    obtain ⟨σ, rfl⟩ := e.surjective u
    have h2 : σ • (show F.obj Z from w) = w :=
      hinj ((hequiv _ w).trans (htrivF σ ((hmem σ).2 hu) (F.map i w)))
    exact (autMulEquivEtaleFundamentalGroup_app_apply σ Z w).trans h2
  · have hsurj : Function.Surjective (F.map i) := fun y => by
      obtain ⟨σ, rfl⟩ := htrans y
      exact ⟨σ • z, by rw [hequiv, hz]⟩
    have hcardA : Nat.card (F.obj A) = Nat.card (Aut F' ⧸ V) :=
      (Nat.card_congr ψ).symm.trans
        (Nat.card_congr ⟨iso.hom.hom, iso.inv.hom, hiso_hom, hiso_hom'⟩)
    have hindex : 2 ≤ Nat.card (Aut F' ⧸ V) := by
      have : Nonempty (F.obj A) := ⟨a₀⟩
      have : Finite (Aut F' ⧸ V) := Nat.finite_of_card_ne_zero (by
        rw [← hcardA]
        exact Nat.card_pos.ne')
      rw [← Subgroup.index]
      exact Subgroup.one_lt_index_of_ne_top hVne
    have hle : Nat.card (F.obj A) ≤ Nat.card (F.obj Z) :=
      Nat.card_le_card_of_surjective _ hsurj
    show 2 ≤ Nat.card (F.obj Z)
    omega

end AlgebraicGeometry

end
