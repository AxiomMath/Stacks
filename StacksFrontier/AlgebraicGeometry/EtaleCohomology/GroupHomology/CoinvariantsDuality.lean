module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.NormalQuotientInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompactCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.PontryaginDualModules

/-!
# Duality between coinvariants and invariants

Let `Γ` be a topological group, `N` a normal subgroup and `M` a compact `Γ`-module. A character
of the coinvariants `M_N` is a character of `M` killing every `g • m - m` with `g ∈ N`, that is,
an `N`-invariant character of `M`. Hence the character group of `H₀(N, M)` is `H⁰(N, M^∧)`, as
discrete `Γ ⧸ N`-modules and naturally in `M`. For `N = Γ` this identifies the character group of
`M_Γ` with the invariants of `M^∧`. This is the identification in degree zero underlying the
trivial duality `H^i(G, M)^∧ = H_i(G, M^∧)` of [Stacks, Tag 03VI], stated here for a compact
module `M`; the statement for a discrete module follows from it by Pontryagin duality.

## Main definitions

* `Stacks.GroupHomology.fixedCharacters N M`: the characters of `M` fixed by `N`.
* `Stacks.GroupHomology.coinvariantsDualEquiv N M`: the characters of `M_N` are the characters
  of `M` fixed by `N`.
* `Stacks.GroupHomology.isoOfAddEquiv`: an isomorphism of discrete `G`-modules from an
  equivariant isomorphism of the underlying groups.
* `Stacks.GroupHomology.normalCoinvariantsDualIso N`: the natural isomorphism
  `H₀(N, M)^∧ ≅ H⁰(N, M^∧)` of discrete `Γ ⧸ N`-modules.
* `Stacks.GroupHomology.compactCoinvariantsDualIso G`: the natural isomorphism
  `(M_G)^∧ ≅ (M^∧)^G` of abelian groups.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.GroupCohomology

universe u v

namespace Stacks.GroupHomology

section Characters

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] (N : Subgroup Γ) (M : CompactGModule.{u, v} Γ)

/-- The characters of a compact `Γ`-module fixed by every element of a subgroup `N`. -/
def fixedCharacters : AddSubgroup (AddPontryaginDual M) where
  carrier := {χ | ∀ g ∈ N, g • χ = χ}
  zero_mem' _ _ := smul_zero _
  add_mem' {χ ψ} hχ hψ g hg := by rw [smul_add, hχ g hg, hψ g hg]
  neg_mem' {χ} hχ g hg := by rw [smul_neg, hχ g hg]

variable {N M}

/-- A character fixed by `N` takes the same value at `g • m` and at `m`, for `g ∈ N`. -/
lemma apply_smul_eq_of_mem_fixedCharacters {χ : AddPontryaginDual M}
    (hχ : χ ∈ fixedCharacters N M) {g : Γ} (hg : g ∈ N) (m : M) : χ (g • m) = χ m := by
  have h := congrArg (fun ψ : AddPontryaginDual M ↦ ψ m) (hχ g⁻¹ (inv_mem hg))
  simpa using h

/-- A character fixed by `N` is trivial on the kernel of the projection onto the coinvariants:
its kernel is a closed subgroup containing every `g • m - m` with `g ∈ N`. -/
lemma apply_eq_one_of_mem_coinvariantsKernel {χ : AddPontryaginDual M}
    (hχ : χ ∈ fixedCharacters N M) {x : M} (hx : x ∈ coinvariantsKernel N M) : χ x = 1 := by
  let S : AddSubgroup M :=
    { carrier := {x | χ x = 1}
      zero_mem' := AddPontryaginDual.map_zero χ
      add_mem' := fun {a b} ha hb ↦ by
        change χ (a + b) = 1
        rw [AddPontryaginDual.map_add, ha, hb, one_mul]
      neg_mem' := fun {a} ha ↦ by
        change χ (-a) = 1
        calc χ (-a) = χ (-a) * χ a := by rw [ha, mul_one]
          _ = 1 := by
            rw [← AddPontryaginDual.map_add, neg_add_cancel, AddPontryaginDual.map_zero] }
  refine coinvariantsKernel_le N M (S := S) (isClosed_singleton.preimage χ.continuous_apply)
    (fun g hg m ↦ ?_) hx
  change χ (g • m - m) = 1
  refine mul_right_cancel (b := χ m) ?_
  rw [← AddPontryaginDual.map_add, sub_add_cancel, one_mul,
    apply_smul_eq_of_mem_fixedCharacters hχ hg]

/-- A character of `M`, as a homomorphism to the additive form of the circle. -/
def toAdditiveHom (χ : AddPontryaginDual M) : M →+ Additive Circle where
  toFun m := Additive.ofMul (χ m)
  map_zero' := by simp
  map_add' a b := by simp

/-- The character of the coinvariants `M_N` induced by a character of `M` fixed by `N`. -/
def descendCharacter (χ : AddPontryaginDual M) (hχ : χ ∈ fixedCharacters N M) :
    AddPontryaginDual (M ⧸ coinvariantsKernel N M) :=
  AddPontryaginDual.mk
    (fun q ↦ Additive.toMul (QuotientAddGroup.lift _ (toAdditiveHom χ)
      (fun x hx ↦ (AddMonoidHom.mem_ker).mpr (by
        change Additive.ofMul (χ x) = Additive.ofMul 1
        rw [apply_eq_one_of_mem_coinvariantsKernel hχ hx])) q))
    (by rw [map_zero]; rfl) (fun a b ↦ by rw [map_add]; rfl)
    ((QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
      (χ.continuous_apply.congr fun _ ↦ rfl))

/-- The induced character of the coinvariants takes the class of `m` to `χ m`. -/
@[simp] lemma descendCharacter_mk (χ : AddPontryaginDual M) (hχ : χ ∈ fixedCharacters N M)
    (m : M) : descendCharacter χ hχ (m : M ⧸ coinvariantsKernel N M) = χ m := rfl

variable (N M)

/-- **The characters of the coinvariants `M_N` are the characters of `M` fixed by `N`**, through
composition with the projection `M → M_N`. -/
def coinvariantsDualEquiv :
    AddPontryaginDual (M ⧸ coinvariantsKernel N M) ≃+ fixedCharacters N M where
  toFun χ := ⟨AddPontryaginDual.comap (compactCoinvariantsMk N M) χ, fun g hg ↦
    AddPontryaginDual.ext fun m ↦ by
      change χ (compactCoinvariantsMk N M (g⁻¹ • m)) = χ (compactCoinvariantsMk N M m)
      rw [compactCoinvariantsMk_smul N M (inv_mem hg)]⟩
  invFun χ := descendCharacter χ.1 χ.2
  left_inv χ := AddPontryaginDual.ext fun x ↦ QuotientAddGroup.induction_on x fun _ ↦ rfl
  right_inv χ := Subtype.ext (AddPontryaginDual.ext fun _ ↦ rfl)
  map_add' _ _ := rfl

/-- The character of `M` attached to a character of `M_N` is its composite with the
projection. -/
@[simp] lemma coinvariantsDualEquiv_apply_apply (χ : AddPontryaginDual (M ⧸ coinvariantsKernel N M))
    (m : M) : (coinvariantsDualEquiv N M χ : AddPontryaginDual M) m = χ m := rfl

end Characters

section Iso

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An isomorphism of discrete `G`-modules given by an equivariant isomorphism of the underlying
abelian groups. -/
def isoOfAddEquiv {X Y : ContinuousGModule.{u, v} G} (e : X.obj.obj.V ≃+ Y.obj.obj.V)
    (he : ∀ (g : G) (x : X.obj.obj.V),
      e ((X.obj.obj.ρ g).asHom.hom x) = (Y.obj.obj.ρ g).asHom.hom (e x)) :
    X ≅ Y where
  hom := (gModuleHomEquiv G X Y).symm ⟨e.toAddMonoidHom, he⟩
  inv := (gModuleHomEquiv G Y X).symm ⟨e.symm.toAddMonoidHom, fun g y ↦ e.injective (by
    change e (e.symm ((Y.obj.obj.ρ g).asHom.hom y)) = e ((X.obj.obj.ρ g).asHom.hom (e.symm y))
    rw [e.apply_symm_apply, he, e.apply_symm_apply])⟩
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ e.symm_apply_apply x)
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun y ↦ e.apply_symm_apply y)

end Iso

section Normal

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (N : Subgroup Γ)
  [N.Normal]

/-- The characters of a compact `Γ`-module fixed by `N` are the `N`-invariants of its character
group. -/
def fixedCharactersEquivNormalInvariants (M : CompactGModule.{u, v} Γ) :
    fixedCharacters N M ≃+ normalInvariants N (discreteDualObj Γ M) where
  toFun χ := ⟨χ.1, (mem_normalInvariants N _).mpr fun g hg ↦ χ.2 g hg⟩
  invFun χ := ⟨χ.1, fun g hg ↦ (mem_normalInvariants N _).mp χ.2 g hg⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The isomorphism `H₀(N, M)^∧ ≅ H⁰(N, M^∧)` of the underlying groups. -/
def normalCoinvariantsDualAddEquiv (M : CompactGModule.{u, v} Γ) :
    ((discreteDual (Γ ⧸ N)).obj (op ((normalCoinvariantsFunctor N).obj M))).obj.obj.V ≃+
      ((normalInvariantsFunctor N).obj ((discreteDual Γ).obj (op M))).obj.obj.V :=
  (coinvariantsDualEquiv N M).trans (fixedCharactersEquivNormalInvariants N M)

/-- **The character group of `H₀(N, M)` is `H⁰(N, M^∧)`**, naturally in the compact `Γ`-module
`M`, as discrete `Γ ⧸ N`-modules: a character of `M_N` is an `N`-invariant character of `M`. -/
def normalCoinvariantsDualIso :
    (normalCoinvariantsFunctor.{u, v} N).op ⋙ discreteDual.{u, v} (Γ ⧸ N) ≅
      discreteDual.{u, v} Γ ⋙ normalInvariantsFunctor.{u, v} N :=
  NatIso.ofComponents
    (fun M ↦ isoOfAddEquiv (normalCoinvariantsDualAddEquiv N M.unop) fun q _ ↦
      QuotientGroup.induction_on q fun _ ↦
        Subtype.ext (AddPontryaginDual.ext (M := M.unop) fun _ ↦ rfl))
    fun {M M'} _ ↦ by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦
        Subtype.ext (AddPontryaginDual.ext (M := M'.unop) fun _ ↦ rfl))

end Normal

section Whole

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying abelian group of a discrete module over the trivial group. -/
abbrev trivialGroupModuleUnderlying : ContinuousGModule.{0, v} PUnit.{1} ⥤ AddCommGrpCat.{v} :=
  Stacks.Injectives.continuousModuleUnderlying ℤ PUnit.{1} ⋙
    forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}

/-- The characters of a compact `G`-module fixed by `G` are the invariants of its character
group. -/
def fixedCharactersEquivInvariants (M : CompactGModule.{u, v} G) :
    fixedCharacters ⊤ M ≃+ ((continuousGModuleInvariants G).obj ((discreteDual G).obj (op M))) where
  toFun χ := ⟨χ.1, fun g ↦ χ.2 g trivial⟩
  invFun χ := ⟨χ.1, fun g _ ↦ χ.2 g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The character group of the coinvariants `M_G` is the group of invariants of `M^∧`**,
naturally in the compact `G`-module `M`. -/
def compactCoinvariantsDualIso :
    (compactCoinvariantsFunctor.{u, v} G).op ⋙ discreteDual.{0, v} PUnit.{1} ⋙
        trivialGroupModuleUnderlying.{v} ≅
      discreteDual.{u, v} G ⋙ continuousGModuleInvariants.{u, v} G :=
  NatIso.ofComponents
    (fun M ↦ AddEquiv.toAddCommGrpIso
      ((coinvariantsDualEquiv ⊤ M.unop).trans (fixedCharactersEquivInvariants G M.unop)))
    fun {_ M'} _ ↦ AddCommGrpCat.ext fun _ ↦
      Subtype.ext (AddPontryaginDual.ext (M := M'.unop) fun _ ↦ rfl)

end Whole

end Stacks.GroupHomology
