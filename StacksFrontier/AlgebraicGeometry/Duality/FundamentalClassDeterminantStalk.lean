module

public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantLocal
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# The pairing of [Stacks, Tag 0E9Y] on stalks

Let `(X, O_X)` be a locally ringed space and let

`E₁ --α--> E₀ --π--> F ⟶ 0`

be a right-exact sequence of sheaves of `O_X`-modules with `E₁` finite locally free of rank
`r₁` and `E₀` finite locally free of rank `r₀ = r₁ + r`. The pairing

`⋀^{r₁} E₁ ⊗_{O_X} ⋀^{r} F ⟶ ⋀^{r₀} E₀`

of `Stacks.Duality.detSheafPairing` is an isomorphism on the stalk at `x` as soon as the stalk
`F_x` is free of rank `r`, hence is an isomorphism of sheaves when `F` is finite locally free of
rank `r`. This is the "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y].

## Main definitions

* `Stacks.Duality.detStalkPairing`: **the stalk at `x` of the sheaf-level map of Tag 0E9Y, read
  as a map of exterior powers of stalk modules**, `⋀^{r₁}(E₁ₓ) ⊗ ⋀^{r}(Fₓ) ⟶ ⋀^{r₁+r}(E₀ₓ)`.
* `Stacks.Duality.detStalkSource`: the identification of its source with the stalk of the
  tensor product sheaf, i.e. Tag 01CB followed by Tag 01CH in each factor.

## Main results

* `Stacks.Duality.surjective_stalkMapL` and
  `Stacks.Duality.range_stalkMapL_eq_ker_stalkMapL`: epimorphy and exactness of sheaves of
  modules, read on the linear stalk maps `PresheafOfModules.stalkMapL`.
* `Stacks.Duality.detStalkPairing_germ` and `Stacks.Duality.detStalkPairing_wedge`: **the stalk
  of the sheaf-level map satisfies the wedge-and-lift formula of Tag 0E9Y**, first on germs of
  local sections over a fixed open and then for arbitrary elements of the stalks.
* `Stacks.Duality.bijective_detStalkPairing` and
  `Stacks.Duality.bijective_stalkMapL_detSheafPairing`: **the "if" half of the criterion at a
  point**, in the two spellings "the transported map is bijective" and "the stalk map of the
  sheaf morphism is bijective".
* `Stacks.Duality.isIso_detSheafPairing`: **the "if" half of the criterion as a statement about
  the sheaf morphism**: it is an isomorphism.
* `Stacks.Duality.isIso_ringedSpaceDetSheafPairing` and
  `Stacks.Duality.isIso_locallyRingedSpaceDetSheafPairing`: the same for *the* exterior powers
  of a ringed space with local stalks, and for a `LocallyRingedSpace`.

## References

* [Stacks Project, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open Stacks.SheafOfModules.TopWedge
open scoped TensorProduct

universe u

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.Duality

section Space

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E₁ E₀ F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-! ### Stalkwise epimorphy and exactness, in linear-map form -/

section Stalkwise

variable {M₂ M₁ M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **A locally surjective morphism of sheaves of modules is surjective on stalks**, as a
statement about `PresheafOfModules.stalkMapL`. -/
theorem surjective_stalkMapL (f : M₁ ⟶ M) [Epi f] (x : ↥X) :
    Function.Surjective (PresheafOfModules.stalkMapL x f.val) :=
  (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap f).1 inferInstance x

/-- **Exactness of a short complex of sheaves of modules, read on a stalk as an equality of a
range and a kernel**, the two stalk maps being linear maps over the stalk of the sheaf of
commutative rings. -/
theorem range_stalkMapL_eq_ker_stalkMapL (q : M₂ ⟶ M₁) (p : M₁ ⟶ M) (hqp : q ≫ p = 0)
    (hex : (ShortComplex.mk q p hqp).Exact) (x : ↥X) :
    LinearMap.range (PresheafOfModules.stalkMapL x q.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x p.val) := by
  have hrk := ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (ShortComplex.mk q p hqp)).1 hex x).moduleCat_range_eq_ker
  refine SetLike.ext fun z => ?_
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.1 (hrk.le (LinearMap.mem_range_self _ y))
  · intro hz
    exact LinearMap.mem_range.1 (hrk.ge (LinearMap.mem_ker.2 hz))

end Stalkwise

variable (A₁ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E₁)
  (A₀ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E₀)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) F)
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r : ℕ)

/-- **The stalk at `x` of the pairing of [Stacks, Tag 0E9Y], read as a map of exterior
powers of stalk modules**

`⋀^{r₁}(E₁ₓ) ⊗_{O_x} ⋀^{r}(Fₓ) ⟶ ⋀^{r₁+r}(E₀ₓ)`.

It is the stalk map of `Stacks.Duality.detSheafPairing` conjugated by the comparison
isomorphisms of [Stacks, Tag 01CB] for the tensor product and of [Stacks, Tag 01CH] for the two
exterior powers in the source and the one in the target. -/
noncomputable def detStalkPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (x : ↥X) :
    ((⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r₁
          ↑(TopCat.Presheaf.stalk E₁.val.presheaf x)) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r
          ↑(TopCat.Presheaf.stalk F.val.presheaf x))) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(r₁ + r)
        ↑(TopCat.Presheaf.stalk E₀.val.presheaf x) :=
  (A₀.exteriorPowerStalkEquiv (r₁ + r) x).toLinearMap ∘ₗ
    (PresheafOfModules.stalkMapL x (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val) ∘ₗ
      ((PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁.exteriorPower r₁)
            (AF.exteriorPower r) x).symm.toLinearMap ∘ₗ
        (TensorProduct.congr (A₁.exteriorPowerStalkEquiv r₁ x).symm
          (AF.exteriorPowerStalkEquiv r x).symm).toLinearMap)

/-- `Stacks.Duality.detStalkPairing` written out as the composite it is defined to be. -/
theorem detStalkPairing_apply [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X)
    (z : (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r₁
          ↑(TopCat.Presheaf.stalk E₁.val.presheaf x)) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r
          ↑(TopCat.Presheaf.stalk F.val.presheaf x))) :
    detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x z =
      A₀.exteriorPowerStalkEquiv (r₁ + r) x
        (PresheafOfModules.stalkMapL x (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val
          ((PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁.exteriorPower r₁)
              (AF.exteriorPower r) x).symm
            (TensorProduct.congr (A₁.exteriorPowerStalkEquiv r₁ x).symm
              (AF.exteriorPowerStalkEquiv r x).symm z))) := rfl

/-- **The wedge-and-lift formula of [Stacks, Tag 0E9Y] on the stalk, for germs of local
sections over a fixed open.** On local sections `t₁, …, t_{r₁}` of `E₁` and `l₁, …, l_{r}` of
`E₀` over an open `U` containing `x`, the stalk map carries
`(germ t₁ ∧ ⋯ ∧ germ t_{r₁}) ⊗ (germ π(l₁) ∧ ⋯ ∧ germ π(l_{r}))` to
`germ α(t₁) ∧ ⋯ ∧ germ α(t_{r₁}) ∧ germ l₁ ∧ ⋯ ∧ germ l_{r}`. -/
theorem detStalkPairing_germ [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (t : Fin r₁ → E₁.val.obj (op U))
    (l : Fin r → E₀.val.obj (op U)) :
    detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r₁
            (fun i => TopCat.Presheaf.germ E₁.val.presheaf U x hx (t i)) ⊗ₜ
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r
            fun i => TopCat.Presheaf.germ F.val.presheaf U x hx
              (π.val.app (op U) (l i))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r₁ + r)
        fun i => TopCat.Presheaf.germ E₀.val.presheaf U x hx
          (Fin.append (fun j => α.val.app (op U) (t j)) l i) := by
  have h1 : (TensorProduct.congr (A₁.exteriorPowerStalkEquiv r₁ x).symm
        (AF.exteriorPowerStalkEquiv r x).symm)
      (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r₁
          (fun i => TopCat.Presheaf.germ E₁.val.presheaf U x hx (t i)) ⊗ₜ
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r
          fun i => TopCat.Presheaf.germ F.val.presheaf U x hx (π.val.app (op U) (l i))) =
      TopCat.Presheaf.germ (A₁.exteriorPower r₁).val.presheaf U x hx
          (wedgeSec A₁ (op U) r₁ t) ⊗ₜ
        TopCat.Presheaf.germ (AF.exteriorPower r).val.presheaf U x hx
          (wedgeSec AF (op U) r fun i => π.val.app (op U) (l i)) := by
    refine (TensorProduct.congr_tmul _ _ _ _).trans ?_
    exact congrArg₂ (fun y z => y ⊗ₜ z)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv_symm_ιMulti_germ A₁ r₁ x U hx t)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv_symm_ιMulti_germ AF r x U hx
        fun i => π.val.app (op U) (l i))
  have h2 : (PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁.exteriorPower r₁)
        (AF.exteriorPower r) x).symm
      (TopCat.Presheaf.germ (A₁.exteriorPower r₁).val.presheaf U x hx
            (wedgeSec A₁ (op U) r₁ t) ⊗ₜ
          TopCat.Presheaf.germ (AF.exteriorPower r).val.presheaf U x hx
            (wedgeSec AF (op U) r fun i => π.val.app (op U) (l i))) =
      PresheafOfModules.tensorSheafGerm Osharp (A₁.exteriorPower r₁)
        (AF.exteriorPower r) x U hx (wedgeSec A₁ (op U) r₁ t)
        (wedgeSec AF (op U) r fun i => π.val.app (op U) (l i)) :=
    (LinearEquiv.symm_apply_eq _).2
      (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp (A₁.exteriorPower r₁)
        (AF.exteriorPower r) x U hx _ _).symm
  have h3 := PresheafOfModules.stalkMapL_germ x
    (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val U hx
    ((PresheafOfModules.tensorSheafUnit (A₁.exteriorPower r₁)
        (AF.exteriorPower r)).app (op U)
      (wedgeSec A₁ (op U) r₁ t ⊗ₜ
        wedgeSec AF (op U) r fun i => π.val.app (op U) (l i)))
  have h4 := detSheafPairing_wedge A₁ A₀ AF α π hαπ hS r₁ r (op U) t
    (fun i => π.val.app (op U) (l i)) l (fun _ => rfl)
  have h5 := _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_wedge A₀ (r₁ + r) x U hx
    (Fin.append (fun j => α.val.app (op U) (t j)) l)
  refine Eq.trans (detStalkPairing_apply A₁ A₀ AF α π hαπ hS r₁ r x _) ?_
  refine Eq.trans (congrArg (fun y => A₀.exteriorPowerStalkEquiv (r₁ + r) x
    (PresheafOfModules.stalkMapL x (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val
      ((PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁.exteriorPower r₁)
        (AF.exteriorPower r) x).symm y))) h1) ?_
  refine Eq.trans (congrArg (fun y => A₀.exteriorPowerStalkEquiv (r₁ + r) x
    (PresheafOfModules.stalkMapL x (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val y)) h2) ?_
  refine Eq.trans (congrArg (A₀.exteriorPowerStalkEquiv (r₁ + r) x) ?_) h5
  exact h3.trans (congrArg
    (TopCat.Presheaf.germ (A₀.exteriorPower (r₁ + r)).val.presheaf U x hx) h4)

/-- **A finite family of germs of one presheaf and a finite family of germs of another are
represented by sections over a single open neighbourhood**, in continuation form: the conclusion
is an arbitrary proposition `p`. -/
theorem forall_common_germ₂ {p : Prop} (P Q : TopCat.Presheaf AddCommGrpCat.{u} X) (x : ↥X)
    (m n : ℕ) (a : Fin m → ↑(TopCat.Presheaf.stalk P x))
    (b : Fin n → ↑(TopCat.Presheaf.stalk Q x))
    (H : ∀ (U : Opens ↥X) (hx : x ∈ U) (s : Fin m → P.obj (op U)) (t : Fin n → Q.obj (op U)),
      (∀ i, TopCat.Presheaf.germ P U x hx (s i) = a i) →
        (∀ i, TopCat.Presheaf.germ Q U x hx (t i) = b i) → p) : p := by
  obtain ⟨U₁, h₁, s₁, hs₁⟩ := _root_.SheafOfModules.SymPresentation.exists_common_germ P x m a
  obtain ⟨U₂, h₂, t₂, ht₂⟩ := _root_.SheafOfModules.SymPresentation.exists_common_germ Q x n b
  refine H (U₁ ⊓ U₂) ⟨h₁, h₂⟩ (fun i => P.map (homOfLE inf_le_left).op (s₁ i))
    (fun i => Q.map (homOfLE inf_le_right).op (t₂ i)) (fun i => ?_) (fun i => ?_)
  · exact (TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_left) x ⟨h₁, h₂⟩ (s₁ i)).trans (hs₁ i)
  · exact (TopCat.Presheaf.germ_res_apply Q (homOfLE inf_le_right) x ⟨h₁, h₂⟩ (t₂ i)).trans
      (ht₂ i)

/-- **The wedge-and-lift formula on germs, through the stalk maps of `α` and `π`.** On local
sections `t₁, …, t_{r₁}` of `E₁` and `l₁, …, l_{r}` of `E₀` over an open `U` containing `x`, the
stalk pairing carries `(germ t₁ ∧ ⋯ ∧ germ t_{r₁}) ⊗ (πₓ(germ l₁) ∧ ⋯ ∧ πₓ(germ l_{r}))` to
`αₓ(germ t₁) ∧ ⋯ ∧ αₓ(germ t_{r₁}) ∧ germ l₁ ∧ ⋯ ∧ germ l_{r}`. -/
theorem detStalkPairing_wedge_germ [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (t : Fin r₁ → E₁.val.obj (op U))
    (l : Fin r → E₀.val.obj (op U)) :
    detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r₁
            (fun i => TopCat.Presheaf.germ E₁.val.presheaf U x hx (t i)) ⊗ₜ
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r
            fun i => PresheafOfModules.stalkMapL x π.val
              (TopCat.Presheaf.germ E₀.val.presheaf U x hx (l i))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r₁ + r)
        (Fin.append
          (fun j => PresheafOfModules.stalkMapL x α.val
            (TopCat.Presheaf.germ E₁.val.presheaf U x hx (t j)))
          fun i => TopCat.Presheaf.germ E₀.val.presheaf U x hx (l i)) := by
  simp only [PresheafOfModules.stalkMapL_germ]
  rw [detStalkPairing_germ]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp

/-- **The stalk of the sheaf-level map of [Stacks, Tag 0E9Y] satisfies the wedge-and-lift
formula of the source, for arbitrary elements of the stalks.** For `v₁, …, v_{r₁}` in `E₁ₓ` and
`u₁, …, u_{r}` in `E₀ₓ`, the stalk of the pairing carries
`(v₁ ∧ ⋯ ∧ v_{r₁}) ⊗ (πₓ(u₁) ∧ ⋯ ∧ πₓ(u_{r}))` to
`αₓ(v₁) ∧ ⋯ ∧ αₓ(v_{r₁}) ∧ u₁ ∧ ⋯ ∧ u_{r}`. -/
theorem detStalkPairing_wedge [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X) (v : Fin r₁ → ↑(TopCat.Presheaf.stalk E₁.val.presheaf x))
    (u : Fin r → ↑(TopCat.Presheaf.stalk E₀.val.presheaf x)) :
    detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r₁ v ⊗ₜ
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r
            fun i => PresheafOfModules.stalkMapL x π.val (u i)) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r₁ + r)
        (Fin.append (fun j => PresheafOfModules.stalkMapL x α.val (v j)) u) := by
  refine forall_common_germ₂ E₁.val.presheaf E₀.val.presheaf x r₁ r v u ?_
  intro U hx t l ht hl
  have e1 := funext ht
  have e2 := funext hl
  subst e1 e2
  exact detStalkPairing_wedge_germ A₁ A₀ AF α π hαπ hS r₁ r x U hx t l

/-- **The "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y] at a point**, for the
transported stalk map: if the stalk of the sheaf of rings is a local ring and the three stalks
are free of ranks `r₁`, `r₁ + r` and `r`, then the stalk of the pairing is bijective. -/
theorem bijective_detStalkPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X) [IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)]
    (b : Module.Basis (Fin r₁) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E₁.val.presheaf x))
    (c₀ : Module.Basis (Fin (r₁ + r)) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E₀.val.presheaf x))
    (dF : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    Function.Bijective (detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x) :=
  bijective_of_wedge_formula (PresheafOfModules.stalkMapL x α.val) b
    (PresheafOfModules.stalkMapL x π.val) (surjective_stalkMapL π x)
    (range_stalkMapL_eq_ker_stalkMapL α π hαπ hS x) c₀ dF
    (detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x)
    (detStalkPairing_wedge A₁ A₀ AF α π hαπ hS r₁ r x)

/-- **The source of `Stacks.Duality.detStalkPairing`, identified with the stalk of the tensor
product sheaf**: the comparison of [Stacks, Tag 01CH] in each exterior factor followed by the
comparison of [Stacks, Tag 01CB] for the tensor product. -/
noncomputable def detStalkSource (x : ↥X) :
    ((⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r₁
          ↑(TopCat.Presheaf.stalk E₁.val.presheaf x)) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r
          ↑(TopCat.Presheaf.stalk F.val.presheaf x)))
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp
        (A₁.exteriorPower r₁) (AF.exteriorPower r)).presheaf x) :=
  (TensorProduct.congr (A₁.exteriorPowerStalkEquiv r₁ x).symm
        (AF.exteriorPowerStalkEquiv r x).symm).trans
    (PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁.exteriorPower r₁)
      (AF.exteriorPower r) x).symm

/-- **The "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y] at a point**, as a
statement about the stalk map of the sheaf morphism itself: if the stalk of the sheaf of rings is
a local ring and the three stalks are free of ranks `r₁`, `r₁ + r` and `r`, then
`Stacks.Duality.detSheafPairing` is bijective on the stalk at `x`. -/
theorem bijective_stalkMapL_detSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    (x : ↥X) [IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)]
    (b : Module.Basis (Fin r₁) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E₁.val.presheaf x))
    (c₀ : Module.Basis (Fin (r₁ + r)) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E₀.val.presheaf x))
    (dF : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x)) :
    Function.Bijective (PresheafOfModules.stalkMapL x
      (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val) := by
  refine (Function.Bijective.of_comp_iff _ (detStalkSource A₁ AF r₁ r x).bijective).1 ?_
  refine ((A₀.exteriorPowerStalkEquiv (r₁ + r) x).bijective.of_comp_iff' _).1 ?_
  exact bijective_detStalkPairing A₁ A₀ AF α π hαπ hS r₁ r x b c₀ dF

/-- **The "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y]: the pairing is an
isomorphism of sheaves of modules.** If every stalk of the sheaf of rings is a local ring — that
is, if `(X, O_X)` is a locally ringed space — and `E₁`, `E₀`, `F` are finite locally free of
ranks `r₁`, `r₁ + r` and `r`, then the pairing

`⋀^{r₁} E₁ ⊗ ⋀^{r} F ⟶ ⋀^{r₁+r} E₀`

is an isomorphism. -/
theorem isIso_detSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ (r₁ + r)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (hloc : ∀ x : ↥X, IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)) :
    IsIso (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r) := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r)).2 fun x => ?_
  have := hloc x
  obtain ⟨e₁⟩ := nonempty_stalkLinearEquiv_finsupp E₁ r₁ x
  obtain ⟨e₀⟩ := nonempty_stalkLinearEquiv_finsupp E₀ (r₁ + r) x
  obtain ⟨eF⟩ := nonempty_stalkLinearEquiv_finsupp F r x
  exact bijective_stalkMapL_detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r x
    (Module.Basis.ofRepr e₁) (Module.Basis.ofRepr e₀) (Module.Basis.ofRepr eF)

end Space

/-! ### The criterion for the exterior powers of a ringed space -/

section RingedSpace

open _root_.Stacks.AlgebraicGeometry RingedSpaceModuleAdjunction

variable (Y : AlgebraicGeometry.RingedSpace.{u, u})
  {E₁ E₀ F : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf)}
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r : ℕ)

/-- **The "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y] for *the* exterior
powers of a ringed space with local stalks.** The exterior powers are those of the package
`SheafOfModules.ringedSpaceAlgebras` of the three algebras that Section 17.21 attaches to a sheaf
of modules on a ringed space. -/
theorem isIso_ringedSpaceDetSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ (r₁ + r)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (hloc : ∀ x : ↥Y.carrier, IsLocalRing ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)) :
    IsIso (ringedSpaceDetSheafPairing Y α π hαπ hS r₁ r) :=
  isIso_detSheafPairing (_root_.SheafOfModules.ringedSpaceAlgebras Y E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y F) α π hαπ hS r₁ r hloc

end RingedSpace

section LocallyRingedSpace

open _root_.Stacks.AlgebraicGeometry RingedSpaceModuleAdjunction

variable (Y : AlgebraicGeometry.LocallyRingedSpace.{u})
  {E₁ E₀ F : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥Y.toRingedSpace.carrier) Y.toRingedSpace.sheaf)}
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r : ℕ)

/-- **The "if" half of the isomorphism criterion of [Stacks, Tag 0E9Y] on a locally ringed
space**: for a right-exact sequence
`E₁ ⟶ E₀ ⟶ F ⟶ 0` of sheaves of modules on a `LocallyRingedSpace` with `E₁`, `E₀` and `F`
finite locally free of ranks `r₁`, `r₁ + r` and `r`, the pairing

`⋀^{r₁} E₁ ⊗ ⋀^{r} F ⟶ ⋀^{r₁+r} E₀`

is an isomorphism. -/
theorem isIso_locallyRingedSpaceDetSheafPairing [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ (r₁ + r)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    IsIso (ringedSpaceDetSheafPairing Y.toRingedSpace α π hαπ hS r₁ r) :=
  isIso_ringedSpaceDetSheafPairing Y.toRingedSpace α π hαπ hS r₁ r fun x => Y.isLocalRing x

end LocallyRingedSpace

end Stacks.Duality

end
