module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.LinearAlgebra.ExteriorPower.LineSubmodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalkNaturality

/-!
# The exterior powers of a sheaf of modules with an invertible subsheaf

Let `(X, O_X)` be a ringed space and `0 → N → E → Q → 0` a short exact sequence of sheaves of
`O_X`-modules with `N` finite locally free of rank one and `Q` finite locally free. For every `k`
the sequence

  `0 → ⋀¹ N ⊗ ⋀ᵏ⁺¹ Q → ⋀ᵏ⁺² E → ⋀ᵏ⁺² Q → 0`

is short exact. Its first map is the comparison
`Stacks.SheafOfModules.TopWedge.detComparison` at `r' = 1`, the descent of the wedge map along
the presentation of [Stacks, Tag 01CJ]; its second map is `⋀ᵏ⁺²` of `E → Q`.

Exactness is stalkwise. At a point the stalk sequence of `0 → N → E → Q → 0` splits, the stalk of
`N` being free of rank one and that of `Q` free; the wedge-and-lift formula
`Stacks.SheafOfModules.TopWedge.detComparison_wedge` identifies the stalk of the first map with
wedging by a generator of the stalk of `N`, and
`exteriorPower.injective_and_range_eq_ker_of_mul` is the linear algebra.

## Main results

* `exteriorPower.injective_and_range_eq_ker_of_mul`: the linear algebra at a point.
* `Stacks.SheafOfModules.TopWedge.stalkComparisonOne_wedge`: the wedge-and-lift formula on stalks.
* `Stacks.SheafOfModules.TopWedge.injective_stalkMapL_detComparison_one` and
  `Stacks.SheafOfModules.TopWedge.exists_stalkMapL_detComparison_one`: the stalk statements.
* `Stacks.SheafOfModules.TopWedge.shortExact_lineComparison`: **the short exact sequence.**
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace exteriorPower

variable {R : Type*} [CommRing R] {P M Q : Type*} [AddCommGroup P] [Module R P]
  [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- `exteriorPower.injective_and_range_eq_ker_of_wedgeLeft` with the target degree a variable
`n = k + 2` and the wedge-and-lift formula read in the exterior algebra. -/
theorem injective_and_range_eq_ker_of_mul (a : P →ₗ[R] M) (g : M →ₗ[R] Q)
    (ha : Function.Injective a) (hg : Function.Surjective g)
    (hex : LinearMap.range a = LinearMap.ker g) (b : Module.Basis (Fin 1) R P)
    [Module.Projective R Q] (k n : ℕ) (hn : n = k + 2)
    (L : P ⊗[R] ⋀[R]^(k + 1) Q →ₗ[R] ⋀[R]^n M)
    (hL : ∀ p y, (L (p ⊗ₜ map (k + 1) g y) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (a p) * (y : ExteriorAlgebra R M)) :
    Function.Injective L ∧ LinearMap.range L = LinearMap.ker (map n g) := by
  subst hn
  refine injective_and_range_eq_ker_of_wedgeLeft a g ha hg hex b k L fun p y ↦ ?_
  exact Subtype.ext ((hL p y).trans (coe_wedgeLeft (a p) (k + 1) y).symm)

/-- A wedge of a concatenated family whose first block has length one is the product of the
generator of that block with the wedge of the second block, in the exterior algebra. -/
theorem coe_ιMulti_append_one {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (k : ℕ) (u : Fin 1 → M) (w : Fin (k + 1) → M) :
    (ιMulti R (1 + (k + 1)) (Fin.append u w) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (u 0) * (ιMulti R (k + 1) w : ExteriorAlgebra R M) := by
  rw [ιMulti_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, Stacks.SheafOfModules.TopWedge.fin_append_comp,
    List.ofFn_fin_append, List.prod_append, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

/-- **The wedge-and-lift formula from its values on wedges.** A linear map out of
`⋀¹ P ⊗ ⋀ᵏ⁺¹ Q` satisfies `L (p ⊗ ⋀ᵏ⁺¹(g)(y)) = a(p) ∧ y` as soon as it does on wedges of
vectors, both sides being bilinear. -/
theorem wedge_formula_of_ιMulti {R : Type*} [CommRing R] {P M Q : Type*} [AddCommGroup P]
    [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q] (k n : ℕ)
    (a : P →ₗ[R] M) (g : M →ₗ[R] Q) (L : ⋀[R]^1 P ⊗[R] ⋀[R]^(k + 1) Q →ₗ[R] ⋀[R]^n M)
    (h : ∀ (v : Fin 1 → P) (w : Fin (k + 1) → M),
      (L (ιMulti R 1 v ⊗ₜ map (k + 1) g (ιMulti R (k + 1) w)) : ExteriorAlgebra R M) =
        ExteriorAlgebra.ι R (a (v 0)) * (ιMulti R (k + 1) w : ExteriorAlgebra R M))
    (p : ⋀[R]^1 P) (y : ⋀[R]^(k + 1) M) :
    (L (p ⊗ₜ map (k + 1) g y) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (a (oneEquiv R P p)) * (y : ExteriorAlgebra R M) := by
  let Φ₁ : ⋀[R]^1 P →ₗ[R] ⋀[R]^(k + 1) M →ₗ[R] ExteriorAlgebra R M :=
    ((TensorProduct.mk R _ _).compr₂ ((⋀[R]^n M).subtype ∘ₗ L)).compl₂ (map (k + 1) g)
  let Φ₂ : ⋀[R]^1 P →ₗ[R] ⋀[R]^(k + 1) M →ₗ[R] ExteriorAlgebra R M :=
    ((LinearMap.mul R (ExteriorAlgebra R M)).comp
      (ExteriorAlgebra.ι R ∘ₗ a ∘ₗ (oneEquiv R P).toLinearMap)).compl₂
        (⋀[R]^(k + 1) M).subtype
  have key : Φ₁ = Φ₂ := by
    refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    refine linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    change (L (ιMulti R 1 v ⊗ₜ map (k + 1) g (ιMulti R (k + 1) w)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (a (oneEquiv R P (ιMulti R 1 v))) *
        (ιMulti R (k + 1) w : ExteriorAlgebra R M)
    rw [oneEquiv_ιMulti]
    exact h v w
  exact DFunLike.congr_fun (DFunLike.congr_fun key p) y

end exteriorPower

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- **A morphism of sheaves of modules all of whose stalk maps vanish is zero**: a section all
of whose germs vanish is zero, and the germ of the image of a section is the stalk map of its
germ. -/
theorem eq_zero_of_stalkMapL_eq_zero
    {M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (v : M ⟶ N)
    (hv : ∀ (y : ↥X) (z : ↑(TopCat.Presheaf.stalk M.val.presheaf y)),
      PresheafOfModules.stalkMapL y v.val z = 0) : v = 0 := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  exact (TopCat.Presheaf.section_ext
    ((AlgebraicGeometry.SheafOfModules.toTopSheaf
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).obj N) V.unop
    (v.val.app V s) 0 fun y hy =>
      (PresheafOfModules.stalkMapL_germ y v.val V.unop hy s).symm.trans
        ((hv y _).trans (map_zero _).symm) : v.val.app V s = 0)

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).Exact)

/-- The induced homomorphism of exterior algebras is the homomorphism of the sequence of
[Stacks, Tag 01CJ]: both are the unique unital homomorphism extending `g`. -/
theorem extHom_eq_extDesc :
    extHom A A'' g =
      _root_.SheafOfModules.ExtPresentation.extDesc A.exteriorGenerator A''.exteriorGenerator
        A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g :=
  rfl

/-- **The stalk of `⋀ⁿ(g)` is `⋀ⁿ` of the stalk of `g`**, read through the comparisons of
[Stacks, Tag 01CH]. -/
theorem exteriorPowerStalkEquiv_stalkMapL_extHom (n : ℕ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)) :
    _root_.SheafOfModules.exteriorPowerStalkEquiv A''.exterior A''.exteriorGenerator
        A''.exterior_isExteriorAlgebra n x
        (PresheafOfModules.stalkMapL x ((extHom A A'' g).app (n : ℤ)).val t) =
      exteriorPower.map n (PresheafOfModules.stalkMapL x g.val)
        (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra n x t) :=
  _root_.SheafOfModules.ExtPresentation.exteriorPowerStalkEquiv_extDesc
    A.exteriorGenerator A''.exteriorGenerator A.exterior_isExteriorAlgebra
    A''.exterior_isExteriorAlgebra g n x t

/-- The stalk of `⋀ⁿ(g)` kills `w` iff `⋀ⁿ` of the stalk of `g` kills its image in the
exterior power of the stalk. -/
private theorem stalkMapL_extHom_eq_zero_iff (n : ℕ) (x : ↥X)
    (w : ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)) :
    PresheafOfModules.stalkMapL x ((extHom A A'' g).app (n : ℤ)).val w = 0 ↔
      exteriorPower.map n (PresheafOfModules.stalkMapL x g.val)
        (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra n x w) = 0 := by
  rw [← exteriorPowerStalkEquiv_stalkMapL_extHom A A'' g n x w,
    ← (_root_.SheafOfModules.exteriorPowerStalkEquiv A''.exterior A''.exteriorGenerator
      A''.exterior_isExteriorAlgebra n x).map_eq_zero_iff]

/-- The stalk of the source of the comparison, identified with
`⋀¹(E'ₓ) ⊗ ⋀ᵏ⁺¹(E''ₓ)`. -/
noncomputable def sourceStalkEquiv (r' k : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r')
          (A''.exteriorPower (k + 1))).presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
    ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r' ↑(TopCat.Presheaf.stalk E'.val.presheaf x)
      ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
        ↑(TopCat.Presheaf.stalk E''.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp (A'.exteriorPower r')
      (A''.exteriorPower (k + 1)) x).trans
    (TensorProduct.congr
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A'.exterior A'.exteriorGenerator
        A'.exterior_isExteriorAlgebra r' x)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A''.exterior A''.exteriorGenerator
        A''.exterior_isExteriorAlgebra (k + 1) x))

/-- `sourceStalkEquiv` sends the germ of `wedgeSec s ⊗ₜ wedgeSec l` to the tensor product of the
wedges of the germs of `s` and the germs of `l`. -/
theorem sourceStalkEquiv_germ (r' k : ℕ) (x : ↥X) (W : Opens ↥X) (hxW : x ∈ W)
    (s : Fin r' → E'.val.obj (op W)) (l : Fin (k + 1) → E''.val.obj (op W)) :
    sourceStalkEquiv A' A'' r' k x
        (TopCat.Presheaf.germ
          (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r')
            (A''.exteriorPower (k + 1))).presheaf W x hxW
          ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
              (A''.exteriorPower (k + 1))).app (op W)
            (wedgeSec A' (op W) r' s ⊗ₜ wedgeSec A'' (op W) (k + 1) l))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r'
          (fun i => TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i)) ⊗ₜ
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
          (fun i => TopCat.Presheaf.germ E''.val.presheaf W x hxW (l i)) := by
  refine Eq.trans (congrArg (TensorProduct.congr
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A'.exterior A'.exteriorGenerator
        A'.exterior_isExteriorAlgebra r' x)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A''.exterior A''.exteriorGenerator
        A''.exterior_isExteriorAlgebra (k + 1) x))
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp (A'.exteriorPower r')
      (A''.exteriorPower (k + 1)) x W hxW _ _)) ?_
  refine Eq.trans (TensorProduct.congr_tmul _ _ _ _) ?_
  exact congrArg₂ (· ⊗ₜ ·)
    (_root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A'.exterior
      A'.exteriorGenerator A'.exterior_isExteriorAlgebra r' x W hxW s)
    (_root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A''.exterior
      A''.exteriorGenerator A''.exterior_isExteriorAlgebra (k + 1) x W hxW l)

/-- The stalk at `x` of `detComparison` for `r' = 1`, read through `sourceStalkEquiv` and
`SheafOfModules.exteriorPowerStalkEquiv`. -/
noncomputable def stalkComparisonOne [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ)
    (x : ↥X) :
    ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^1 ↑(TopCat.Presheaf.stalk E'.val.presheaf x)
        ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
          ↑(TopCat.Presheaf.stalk E''.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(1 + (k + 1))
        ↑(TopCat.Presheaf.stalk E.val.presheaf x) :=
  (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra (1 + (k + 1)) x).toLinearMap ∘ₗ
    PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val ∘ₗ
      (sourceStalkEquiv A' A'' 1 k x).symm.toLinearMap

/-- `stalkComparisonOne` is the composite of the inverse of `sourceStalkEquiv`, the stalk map of
`detComparison` and `SheafOfModules.exteriorPowerStalkEquiv`. -/
theorem stalkComparisonOne_apply [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ)
    (x : ↥X) (z : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^1
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
        ↑(TopCat.Presheaf.stalk E''.val.presheaf x)) :
    stalkComparisonOne A' A A'' f g hfg hS k x z =
      _root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
        A.exterior_isExteriorAlgebra (1 + (k + 1)) x
        (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val
          ((sourceStalkEquiv A' A'' 1 k x).symm z)) :=
  rfl

/-- **The wedge-and-lift formula on stalks**, on germs of wedges of sections over one
neighbourhood. -/
theorem stalkComparisonOne_germ [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ)
    (x : ↥X) (W : Opens ↥X) (hxW : x ∈ W) (s : Fin 1 → E'.val.obj (op W))
    (l : Fin (k + 1) → E.val.obj (op W)) :
    stalkComparisonOne A' A A'' f g hfg hS k x
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) 1
            (fun i => TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i)) ⊗ₜ
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
            fun j => TopCat.Presheaf.germ E''.val.presheaf W x hxW (g.val.app (op W) (l j))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (1 + (k + 1))
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
          (Fin.append (fun i' => f.val.app (op W) (s i')) l i) := by
  have hsym : (sourceStalkEquiv A' A'' 1 k x).symm
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) 1
            (fun i => TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i)) ⊗ₜ
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
            fun j => TopCat.Presheaf.germ E''.val.presheaf W x hxW (g.val.app (op W) (l j))) =
      TopCat.Presheaf.germ
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower 1)
          (A''.exteriorPower (k + 1))).presheaf W x hxW
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower 1)
            (A''.exteriorPower (k + 1))).app (op W)
          (wedgeSec A' (op W) 1 s ⊗ₜ
            wedgeSec A'' (op W) (k + 1) fun j => g.val.app (op W) (l j))) :=
    (sourceStalkEquiv A' A'' 1 k x).symm_apply_eq.2
      (sourceStalkEquiv_germ A' A'' 1 k x W hxW s fun j => g.val.app (op W) (l j)).symm
  refine Eq.trans (stalkComparisonOne_apply A' A A'' f g hfg hS k x _) ?_
  refine Eq.trans (congrArg (fun z => _root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior
      A.exteriorGenerator A.exterior_isExteriorAlgebra (1 + (k + 1)) x
      (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val z)) hsym) ?_
  refine Eq.trans (congrArg (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior
      A.exteriorGenerator A.exterior_isExteriorAlgebra (1 + (k + 1)) x)
    ((PresheafOfModules.stalkMapL_germ x (detComparison A' A A'' f g hfg hS 1 k).val W hxW _).trans
      (congrArg (TopCat.Presheaf.germ (A.exteriorPower (1 + (k + 1))).val.presheaf W x hxW)
        (detComparison_wedge A' A A'' f g hfg hS 1 k (op W) s l)))) ?_
  exact _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A.exterior
    A.exteriorGenerator A.exterior_isExteriorAlgebra (1 + (k + 1)) x W hxW _

/-- **The wedge-and-lift formula on stalks**: the stalk of the comparison at `r' = 1` sends
`p ⊗ ⋀ᵏ⁺¹(gₓ)(y)` to `fₓ(p) ∧ y`. -/
theorem stalkComparisonOne_wedge [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ)
    (x : ↥X) (p : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^1
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (y : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :
    (stalkComparisonOne A' A A'' f g hfg hS k x
        (p ⊗ₜ exteriorPower.map (k + 1) (PresheafOfModules.stalkMapL x g.val) y) :
        ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)) =
      ExteriorAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          (PresheafOfModules.stalkMapL x f.val (exteriorPower.oneEquiv
            ↑(TopCat.Presheaf.stalk Osharp.obj x) ↑(TopCat.Presheaf.stalk E'.val.presheaf x) p)) *
        (y : ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)) := by
  refine exteriorPower.wedge_formula_of_ιMulti k (1 + (k + 1))
    (PresheafOfModules.stalkMapL x f.val) (PresheafOfModules.stalkMapL x g.val)
    (stalkComparisonOne A' A A'' f g hfg hS k x) (fun v w => ?_) p y
  refine (exists_common_germ E' E x v w).elim fun W hW => hW.elim fun hxW hW' =>
    hW'.elim fun s hs' => hs'.elim fun l hsl => ?_
  have hv : v = fun i => TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i) :=
    (funext hsl.1).symm
  have hw : w = fun j => TopCat.Presheaf.germ E.val.presheaf W x hxW (l j) :=
    (funext hsl.2).symm
  subst hv
  subst hw
  refine Eq.trans (congrArg (fun z => ((stalkComparisonOne A' A A'' f g hfg hS k x
      (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) 1
        (fun i => TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i)) ⊗ₜ z) :
        ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(1 + (k + 1))
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :
      ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)))
    ((exteriorPower.map_apply_ιMulti _ _).trans
      (congrArg _ (funext fun j => PresheafOfModules.stalkMapL_germ x g.val W hxW (l j))))) ?_
  refine Eq.trans (congrArg Subtype.val
    (stalkComparisonOne_germ A' A A'' f g hfg hS k x W hxW s l)) ?_
  refine Eq.trans (congrArg (fun t => (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x)
      (1 + (k + 1)) t : ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)))
    (fin_append_comp (fun y => TopCat.Presheaf.germ E.val.presheaf W x hxW y)
      (fun i' => f.val.app (op W) (s i')) l)) ?_
  refine Eq.trans (exteriorPower.coe_ιMulti_append_one k _ _) ?_
  exact congrArg (fun z => ExteriorAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x) z *
      (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1)
        (fun j => TopCat.Presheaf.germ E.val.presheaf W x hxW (l j)) :
        ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)))
    (PresheafOfModules.stalkMapL_germ x f.val W hxW (s 0)).symm

/-- **The stalk statement.** At every point the stalk of the comparison at `r' = 1` is injective
and its image is the kernel of the stalk of `⋀ᵏ⁺²(g)`, read through the comparisons of Tag 01CH. -/
theorem stalkComparisonOne_injective_range [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ)
    (x : ↥X) :
    Function.Injective (stalkComparisonOne A' A A'' f g hfg hS k x) ∧
      LinearMap.range (stalkComparisonOne A' A A'' f g hfg hS k x) =
        LinearMap.ker (exteriorPower.map (1 + (k + 1)) (PresheafOfModules.stalkMapL x g.val)) := by
  have hse := stalkMapL_shortExact f g hfg hS x
  have hinj := hse.1
  have hsurj := hse.2.1
  have hex := hse.2.2
  have : Module.Projective ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x) :=
    Module.Projective.of_basis (stalkBasis E'' m x)
  have hainj : Function.Injective (PresheafOfModules.stalkMapL x f.val ∘ₗ
      (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x)).toLinearMap) :=
    hinj.comp (exteriorPower.oneEquiv _ _).injective
  have harange : LinearMap.range (PresheafOfModules.stalkMapL x f.val ∘ₗ
      (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x)).toLinearMap) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, hex]
  have hL : ∀ p y, (stalkComparisonOne A' A A'' f g hfg hS k x
        (p ⊗ₜ exteriorPower.map (k + 1) (PresheafOfModules.stalkMapL x g.val) y) :
        ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)) =
      ExteriorAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ((PresheafOfModules.stalkMapL x f.val ∘ₗ
            (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk E'.val.presheaf x)).toLinearMap) p) *
        (y : ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :=
    fun p y => stalkComparisonOne_wedge A' A A'' f g hfg hS k x p y
  have hb : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^1 ↑(TopCat.Presheaf.stalk E'.val.presheaf x)) :=
    (stalkBasis E' 1 x).map (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x)).symm
  exact exteriorPower.injective_and_range_eq_ker_of_mul
    (PresheafOfModules.stalkMapL x f.val ∘ₗ
      (exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x)).toLinearMap)
    (PresheafOfModules.stalkMapL x g.val) hainj hsurj harange hb k (1 + (k + 1)) (by omega)
    (stalkComparisonOne A' A A'' f g hfg hS k x) hL

/-- The stalk comparison on the image of `sourceStalkEquiv` is the stalk of the comparison. -/
theorem stalkComparisonOne_sourceStalkEquiv [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ)
    (x : ↥X) (t : ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower 1)
          (A''.exteriorPower (k + 1))).presheaf x)) :
    stalkComparisonOne A' A A'' f g hfg hS k x (sourceStalkEquiv A' A'' 1 k x t) =
      _root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
        A.exterior_isExteriorAlgebra (1 + (k + 1)) x
        (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val t) :=
  (stalkComparisonOne_apply A' A A'' f g hfg hS k x _).trans
    (congrArg (fun t' => _root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior
      A.exteriorGenerator A.exterior_isExteriorAlgebra (1 + (k + 1)) x
      (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val t'))
      ((sourceStalkEquiv A' A'' 1 k x).symm_apply_apply t))

/-- **The stalk of the comparison at `r' = 1` is injective.** -/
theorem injective_stalkMapL_detComparison_one [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ)
    (x : ↥X) :
    Function.Injective
      (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val) := by
  intro z z' hzz'
  have hinj := (stalkComparisonOne_injective_range A' A A'' f g hfg hS m k x).1
  have h := congrArg (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior
    A.exteriorGenerator A.exterior_isExteriorAlgebra (1 + (k + 1)) x) hzz'
  refine (sourceStalkEquiv A' A'' 1 k x).injective (hinj ?_)
  exact (stalkComparisonOne_sourceStalkEquiv A' A A'' f g hfg hS k x z).trans
    (h.trans (stalkComparisonOne_sourceStalkEquiv A' A A'' f g hfg hS k x z').symm)

/-- **The stalk of the comparison at `r' = 1` lands in the kernel of `⋀ᵏ⁺²(gₓ)`.** -/
theorem map_stalkMapL_detComparison_one [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ)
    (x : ↥X) (ξ : ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower 1)
          (A''.exteriorPower (k + 1))).presheaf x)) :
    exteriorPower.map (1 + (k + 1)) (PresheafOfModules.stalkMapL x g.val)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
        A.exterior_isExteriorAlgebra (1 + (k + 1)) x
        (PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val ξ)) = 0 := by
  have hrange := (stalkComparisonOne_injective_range A' A A'' f g hfg hS m k x).2
  have hker : stalkComparisonOne A' A A'' f g hfg hS k x (sourceStalkEquiv A' A'' 1 k x ξ) ∈
      LinearMap.ker (exteriorPower.map (1 + (k + 1)) (PresheafOfModules.stalkMapL x g.val)) :=
    hrange.le (LinearMap.mem_range_self _ _)
  exact (congrArg (exteriorPower.map (1 + (k + 1)) (PresheafOfModules.stalkMapL x g.val))
    (stalkComparisonOne_sourceStalkEquiv A' A A'' f g hfg hS k x ξ)).symm.trans
      (LinearMap.mem_ker.1 hker)

/-- **The kernel of the stalk of `⋀ᵏ⁺²(g)` is the image of the stalk of the comparison.** -/
theorem exists_stalkMapL_detComparison_one [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ)
    (x : ↥X) (w : ↑(TopCat.Presheaf.stalk (A.exteriorPower (1 + (k + 1))).val.presheaf x))
    (hw : exteriorPower.map (1 + (k + 1)) (PresheafOfModules.stalkMapL x g.val)
      (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
        A.exterior_isExteriorAlgebra (1 + (k + 1)) x w) = 0) :
    ∃ ξ, PresheafOfModules.stalkMapL x (detComparison A' A A'' f g hfg hS 1 k).val ξ = w := by
  obtain ⟨t, ht⟩ :=
    (stalkComparisonOne_injective_range A' A A'' f g hfg hS m k x).2.ge (LinearMap.mem_ker.2 hw)
  refine ⟨(sourceStalkEquiv A' A'' 1 k x).symm t,
    (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra (1 + (k + 1)) x).injective ?_⟩
  exact (stalkComparisonOne_apply A' A A'' f g hfg hS k x t).symm.trans ht

/-- The source `⋀¹ N ⊗ ⋀ᵏ⁺¹ Q` of the comparison at `r' = 1`, as a sheaf of modules over the
structure sheaf. -/
noncomputable abbrev lineSource (k : ℕ) :
    _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) :=
  (show _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⥤
      _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) from
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj
      (A'.exteriorPower 1)).obj (A''.exteriorPower (k + 1))

/-- The comparison at `r' = 1` with source `lineSource`. -/
noncomputable abbrev lineComparison [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (k : ℕ) :
    lineSource A' A'' k ⟶ A.exteriorPower (1 + (k + 1)) :=
  detComparison A' A A'' f g hfg hS 1 k

/-- The composite of the comparison at `r' = 1` with `⋀ᵏ⁺²(g)` vanishes. -/
theorem lineComparison_comp_extHom [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ) :
    lineComparison A' A A'' f g hfg hS k ≫ (extHom A A'' g).app ((1 + (k + 1) : ℕ) : ℤ) = 0 := by
  refine eq_zero_of_stalkMapL_eq_zero _ fun x z => ?_
  refine (PresheafOfModules.stalkMapL_comp_apply x (detComparison A' A A'' f g hfg hS 1 k).val
    ((extHom A A'' g).app ((1 + (k + 1) : ℕ) : ℤ)).val z).symm.trans ?_
  rw [stalkMapL_extHom_eq_zero_iff]
  exact map_stalkMapL_detComparison_one A' A A'' f g hfg hS m k x z

/-- **The exterior powers of a sheaf of modules with an invertible subsheaf.** For a short exact
sequence `0 → N → E → Q → 0` of sheaves of modules on a ringed space with `N` finite locally free
of rank one and `Q` finite locally free of constant rank, the sequence

  `0 → ⋀¹ N ⊗ ⋀ᵏ⁺¹ Q → ⋀ᵏ⁺² E → ⋀ᵏ⁺² Q → 0`

is short exact, its first map being the comparison of Tag 0B38 at `r' = 1` and its second
`⋀ᵏ⁺²` of `E → Q`. -/
theorem shortExact_lineComparison [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] (k : ℕ) :
    (ShortComplex.mk (lineComparison A' A A'' f g hfg hS k)
      ((extHom A A'' g).app ((1 + (k + 1) : ℕ) : ℤ))
      (lineComparison_comp_extHom A' A A'' f g hfg hS m k)).ShortExact := by
  have hepi : Epi ((extHom A A'' g).app ((1 + (k + 1) : ℕ) : ℤ)) :=
    _root_.SheafOfModules.ExtPresentation.epi_extDesc_app A.exteriorGenerator
      A''.exteriorGenerator A.exterior_isExteriorAlgebra A''.exterior_isExteriorAlgebra g
      (1 + (k + 1))
  have hmono : Mono (lineComparison A' A A'' f g hfg hS k) :=
    (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap _).2 fun x z z' hzz' =>
      injective_stalkMapL_detComparison_one A' A A'' f g hfg hS m k x
        ((stalkMap_hom_apply _ x z).symm.trans (hzz'.trans (stalkMap_hom_apply _ x z')))
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun w hw => ?_
  have hmap := (stalkMapL_extHom_eq_zero_iff A A'' g (1 + (k + 1)) x w).1
    ((stalkMap_hom_apply _ x w).symm.trans hw)
  obtain ⟨ξ, hξ⟩ := exists_stalkMapL_detComparison_one A' A A'' f g hfg hS m k x w hmap
  exact ⟨ξ, (stalkMap_hom_apply _ x ξ).trans hξ⟩

end Stacks.SheafOfModules.TopWedge
