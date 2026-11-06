module

public import StacksFrontier.Algebra.Module.GroupAlgebraDualHom
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianAcyclicModuleAcyclic

/-!
# The descent sheaf `D(M)` as `Hom_{A[H]}(M^*, D(A[H]))`

Let `G : V ⟶ X` be a Galois covering with finite group `H`, `A = ℤ/n`, and `M` a finite
`ℤ/n`-module with an action `ρ` of `H` commuting with a ring `Λ`. Write `D(A[H])` for the descent
sheaf of the regular representation (the sheaf `f_* A` with its `A[H]`-module structure,
`AlgebraicGeometry.EtaleGaloisCovering.regularDescentSheaf`) and `M^* = Hom_A(M, A)`, an
`(A[H], Λ)`-bimodule (`Stacks.GroupAlgebraDual.Dual`). Applying `Hom_{A[H]}(M^*, -)` sectionwise
to `D(A[H])` gives the descent sheaf `D(M)` of `M`:

`Hom_{A[H]}(M^*, D(A[H])) ≅ D(M)`.

Over `W`, a section of the right side is an `H`-equivariant locally constant map
`c : V ×_X W → M`; it corresponds to `n ↦ (z ↦ ∑_g n(g c(z)) g)`, an `A[H]`-linear map from `M^*`
to the equivariant locally constant maps `V ×_X W → A[H]`
(`Stacks.GroupAlgebraDual.ofM_bijective`).

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.dualHomDescentIso`: the isomorphism
  `Hom_{A[H]}(M^*, D(A[H])) ≅ D(M)` of sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 4–7.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidAlgebra Stacks.GroupAlgebraDual

universe u

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type} [Group H] [Fintype H] (G : EtaleGaloisCovering X H)
  (n : ℕ) [NeZero n] (Λ : Type) [Ring Λ] {M : Type (u + 1)} [AddCommGroup M] [Module Λ M]
  [Module (ZMod n) M] [Finite M] (ρ : H →* Module.End Λ M)

/-- The dual `M^* = Hom_A(M, A)` of a finite module is finite. -/
instance : Finite (Dual n ρ) :=
  Finite.of_equiv _ ((zmodRep n ρ).dual.asModuleEquiv.symm.toEquiv)

/-- The sections over `W` of `D(A[H])`. -/
abbrev RegularSections (W : X.Etale) : Type (u + 1) :=
  G.equivariantMaps (MonoidAlgebra (ZMod n) H) (ULift.{u + 1} (MonoidAlgebra (ZMod n) H))
    (rightRegularRepULift.{u} (ZMod n) H) W

variable {n Λ ρ}

/-- The equivariant locally constant map `z ↦ ∑_g n(g c(z)) g` attached to `c ∈ D(M)(W)` and
`n ∈ M^*`. -/
def dualHomValue {W : X.Etale} (c : G.equivariantMaps Λ M ρ W) (φ : Dual n ρ) :
    G.RegularSections n W :=
  ⟨c.1.map fun m ↦ ULift.up (ofM m φ), fun h z ↦ by
    change ULift.up (ofM (c.1 ((G.pullbackAct W h).base z)) φ) =
      ULift.up (ofM (c.1 z) φ * single h⁻¹ 1)
    rw [c.2 h z, ofM_rho]⟩

omit [NeZero n] [Finite M] in
/-- The value of `dualHomValue c φ` at `z` is `∑_g φ(g c(z)) g`. -/
@[simp]
lemma dualHomValue_apply {W : X.Etale} (c : G.equivariantMaps Λ M ρ W) (φ : Dual n ρ)
    (z : G.fiberProd W) : ((G.dualHomValue c φ).1 z).down = ofM (c.1 z) φ := rfl

/-- The `A[H]`-linear map `M^* → D(A[H])(W)` attached to `c ∈ D(M)(W)`. -/
def dualHomOfSection {W : X.Etale} (c : G.equivariantMaps Λ M ρ W) :
    ModuleCat.BimoduleHom.Obj (MonoidAlgebra (ZMod n) H) (Dual n ρ) (G.RegularSections n W) :=
  (ModuleCat.BimoduleHom.toLinearMap _).symm
    { toFun := G.dualHomValue c
      map_add' φ ψ := Subtype.ext (LocallyConstant.ext fun z ↦ ULift.ext (by
        change ofM (c.1 z) (φ + ψ) = ofM (c.1 z) φ + ofM (c.1 z) ψ
        exact map_add _ _ _))
      map_smul' r φ := Subtype.ext (LocallyConstant.ext fun z ↦ ULift.ext (by
        change ofM (c.1 z) (r • φ) = r * ofM (c.1 z) φ
        exact map_smul _ _ _)) }

omit [NeZero n] [Finite M] in
/-- The value at `φ` and `z` of `dualHomOfSection c` is `∑_g φ(g c(z)) g`. -/
lemma dualHomOfSection_apply {W : X.Etale} (c : G.equivariantMaps Λ M ρ W) (φ : Dual n ρ)
    (z : G.fiberProd W) :
    ((ModuleCat.BimoduleHom.toLinearMap _ (G.dualHomOfSection c) φ).1 z).down =
      ofM (c.1 z) φ := rfl

variable (n Λ ρ) in
/-- `c ↦ (φ ↦ (z ↦ ∑_g φ(g c(z)) g))`, as a `Λ`-linear map
`D(M)(W) → Hom_{A[H]}(M^*, D(A[H])(W))`. -/
def dualHomLinear (W : X.Etale) :
    G.equivariantMaps Λ M ρ W →ₗ[Λ]
      ModuleCat.BimoduleHom.Obj (MonoidAlgebra (ZMod n) H) (Dual n ρ) (G.RegularSections n W) where
  toFun := G.dualHomOfSection
  map_add' c c' := (ModuleCat.BimoduleHom.ext_iff' _).2 fun φ ↦ Subtype.ext
    (LocallyConstant.ext fun z ↦ ULift.ext (by
      change ofM (c.1 z + c'.1 z) φ = ofM (c.1 z) φ + ofM (c'.1 z) φ
      rw [ofM_add, LinearMap.add_apply]))
  map_smul' l c := (ModuleCat.BimoduleHom.ext_iff' _).2 fun φ ↦ Subtype.ext
    (LocallyConstant.ext fun z ↦ ULift.ext (by
      change ofM (l • c.1 z) φ = ofM (c.1 z) (MulOpposite.op l • φ)
      rw [ofM_smul]))

/-- The values over a point `z` of an `A[H]`-linear map `M^* → D(A[H])(W)`. -/
def pointEval {W : X.Etale}
    (Ψ : ModuleCat.BimoduleHom.Obj (MonoidAlgebra (ZMod n) H) (Dual n ρ) (G.RegularSections n W))
    (z : G.fiberProd W) : Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H where
  toFun φ := ((ModuleCat.BimoduleHom.toLinearMap _ Ψ φ).1 z).down
  map_add' φ ψ := by rw [map_add]; rfl
  map_smul' r φ := by rw [map_smul]; rfl

omit [Fintype H] in
/-- The point values of an `A[H]`-linear map `M^* → D(A[H])(W)` are locally constant. -/
lemma isLocallyConstant_pointEval {W : X.Etale}
    (Ψ : ModuleCat.BimoduleHom.Obj (MonoidAlgebra (ZMod n) H) (Dual n ρ) (G.RegularSections n W)) :
    IsLocallyConstant (G.pointEval Ψ) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun z ↦ ?_
  let f : Dual n ρ → LocallyConstant (G.fiberProd W) (ULift.{u + 1} (MonoidAlgebra (ZMod n) H)) :=
    fun φ ↦ (ModuleCat.BimoduleHom.toLinearMap _ Ψ φ).1
  refine ⟨⋂ φ, f φ ⁻¹' {f φ z},
    isOpen_iInter_of_finite fun φ ↦ (f φ).isLocallyConstant.isOpen_fiber _,
    Set.mem_iInter.2 fun φ ↦ rfl, fun z' hz' ↦ LinearMap.ext fun φ ↦ ?_⟩
  exact congrArg ULift.down (Set.mem_iInter.1 hz' φ)

/-- `c ↦ (φ ↦ (z ↦ ∑_g φ(g c(z)) g))` is a bijection `D(M)(W) → Hom_{A[H]}(M^*, D(A[H])(W))`. -/
lemma dualHomLinear_bijective (W : X.Etale) : Function.Bijective (G.dualHomLinear n Λ ρ W) := by
  refine ⟨fun c c' h ↦ Subtype.ext (LocallyConstant.ext fun z ↦ ofM_injective (n := n) (ρ := ρ)
      (LinearMap.ext fun φ ↦ ?_)), fun Ψ ↦ ?_⟩
  · exact congrArg (fun Ψ ↦ ((ModuleCat.BimoduleHom.toLinearMap _ Ψ φ).1 z).down) h
  · let e := Equiv.ofBijective _ (ofM_bijective (n := n) (ρ := ρ))
    let c₀ : LocallyConstant (G.fiberProd W) M :=
      ⟨fun z ↦ e.symm (G.pointEval Ψ z), (G.isLocallyConstant_pointEval Ψ).comp _⟩
    have hc₀ : ∀ z, ofM (c₀ z) = G.pointEval Ψ z := fun z ↦ e.apply_symm_apply _
    refine ⟨⟨c₀, fun h z ↦ ofM_injective (n := n) (ρ := ρ) ?_⟩, ?_⟩
    · refine LinearMap.ext fun φ ↦ ?_
      rw [ofM_rho, hc₀, hc₀]
      exact congrArg ULift.down ((ModuleCat.BimoduleHom.toLinearMap _ Ψ φ).2 h z)
    · refine (ModuleCat.BimoduleHom.ext_iff' _).2 fun φ ↦ Subtype.ext
        (LocallyConstant.ext fun z ↦ ULift.ext ?_)
      change ofM (c₀ z) φ = G.pointEval Ψ z φ
      rw [hc₀]

/-- The isomorphism `D(M)(W) ≅ Hom_{A[H]}(M^*, D(A[H])(W))`. -/
def dualHomLinearEquiv (W : X.Etale) :
    G.equivariantMaps Λ M ρ W ≃ₗ[Λ]
      ModuleCat.BimoduleHom.Obj (MonoidAlgebra (ZMod n) H) (Dual n ρ) (G.RegularSections n W) :=
  LinearEquiv.ofBijective _ (G.dualHomLinear_bijective W)

variable (n Λ ρ) in
/-- **`Hom_{A[H]}(M^*, D(A[H])) ≅ D(M)`**: applying `Hom_{A[H]}(M^*, -)` sectionwise to the
regular descent sheaf gives the descent sheaf of `M`. -/
def dualHomDescentIso :
    (sheafCompose X.smallEtaleTopology
        (ModuleCat.BimoduleHom.functor (MonoidAlgebra (ZMod n) H) Λ (Dual n ρ))).obj
      (G.regularDescentSheaf (A := ZMod n)) ≅ G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun W ↦ (G.dualHomLinearEquiv (n := n) (ρ := ρ) W.unop).toModuleIso.symm)
      fun {W W'} g ↦ by
        ext Ψ : 2
        apply (G.dualHomLinearEquiv (n := n) (ρ := ρ) W'.unop).injective
        refine (ModuleCat.BimoduleHom.ext_iff' _).2 fun φ ↦ Subtype.ext
          (LocallyConstant.ext fun z ↦ ULift.ext ?_)
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
        refine (congrArg (fun Ψ' ↦ ((ModuleCat.BimoduleHom.toLinearMap _ Ψ' φ).1 z).down)
          ((G.dualHomLinearEquiv (n := n) (ρ := ρ) W'.unop).apply_symm_apply _)).trans ?_
        change ((ModuleCat.BimoduleHom.toLinearMap _ Ψ φ).1 ((G.pullbackMap g.unop).base z)).down =
          ofM (n := n) (ρ := ρ) (((G.dualHomLinearEquiv (n := n) (ρ := ρ) W.unop).symm Ψ).1
            ((G.pullbackMap g.unop).base z)) φ
        rw [← G.dualHomOfSection_apply]
        exact congrArg (fun Ψ' ↦ ((ModuleCat.BimoduleHom.toLinearMap _ Ψ' φ).1
          ((G.pullbackMap g.unop).base z)).down)
          ((G.dualHomLinearEquiv (n := n) (ρ := ρ) W.unop).apply_symm_apply Ψ).symm)

end AlgebraicGeometry.EtaleGaloisCovering

end
