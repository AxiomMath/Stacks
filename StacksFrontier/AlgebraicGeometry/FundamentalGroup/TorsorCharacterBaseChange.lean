module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCharacter
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap

/-!
# Base change of torsor covers and their characters

Let `T` be a `K`-torsor cover of a connected scheme `X` (`AlgebraicGeometry.TorsorCover`) and
`f : Y ⟶ X` a morphism from a connected scheme. The base change `T ×_X Y`, with the base-changed
action of `K`, is a `K`-torsor cover of `Y`: its fibre at a geometric point `ȳ` is the fibre of
`T` at `f(ȳ)`, compatibly with the action. Its character is the character of `T` composed with
`f_* : π₁(Y, ȳ) → π₁(X, f(ȳ))`: both describe how `π₁(Y, ȳ)` moves the points of the common
fibre, and `f_*` is characterised by its action on fibres of base-changed covers
(`AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection`, Tag 0BND (3)).

## Main definitions

* `AlgebraicGeometry.TorsorCover.baseChange`: the torsor cover `T ×_X Y` of `Y`.

## Main results

* `AlgebraicGeometry.TorsorCover.baseChange_character`: its character is `χ_T ∘ f_*`.
* `AlgebraicGeometry.TorsorCover.character_eq_of_hom`: an equivariant morphism of torsor covers
  preserves the character.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace TorsorCover

variable {X Y : Scheme.{u}} {K : Type*} [AddCommGroup K] (T : TorsorCover X K) (f : Y ⟶ X)

/-- The fibre projections intertwine the base-changed action with the action. -/
public theorem finiteEtaleFiberProjection_map_τ (y : GeometricPoint Y) (a : K)
    (p : (finiteEtaleFiberFunctor y).obj ((finiteEtaleBaseChange f).obj T.cover)) :
    finiteEtaleFiberProjection f y T.cover
        ((finiteEtaleFiberFunctor y).map ((finiteEtaleBaseChange f).map (T.τ a)) p) =
      (finiteEtaleFiberFunctor (y.map f)).map (T.τ a) (finiteEtaleFiberProjection f y T.cover p) :=
  Subtype.ext ((Category.assoc _ _ _).trans ((congrArg (p.1 ≫ ·)
    (finiteEtaleBaseChange_map_left_fst f (T.τ a))).trans (Category.assoc _ _ _).symm))

/-- **The base change `T ×_X Y` of a torsor cover, a torsor cover of `Y`.** -/
public def baseChange : TorsorCover Y K where
  cover := (finiteEtaleBaseChange f).obj T.cover
  τ a := (finiteEtaleBaseChange f).map (T.τ a)
  τ_zero := by rw [T.τ_zero, CategoryTheory.Functor.map_id]
  τ_add a b := by rw [T.τ_add, CategoryTheory.Functor.map_comp]
  existsUnique y p q := by
    obtain ⟨a, ha, hu⟩ := T.existsUnique (y.map f) (finiteEtaleFiberProjection f y T.cover p)
      (finiteEtaleFiberProjection f y T.cover q)
    refine ⟨a, (finiteEtaleFiberProjectionEquiv f y T.cover).injective ?_, fun b hb => hu b ?_⟩
    · exact (finiteEtaleFiberProjection_map_τ T f y a p).trans ha
    · exact (finiteEtaleFiberProjection_map_τ T f y b p).symm.trans
        (congrArg (finiteEtaleFiberProjection f y T.cover) hb)

/-- **An equivariant morphism of torsor covers preserves the character**: `π₁` and `K` both
act on the fibres through the morphism. -/
public theorem character_eq_of_hom [ConnectedSpace X] {T₁ T₂ : TorsorCover X K}
    (h : T₁.cover ⟶ T₂.cover) (hh : ∀ a, T₁.τ a ≫ h = h ≫ T₂.τ a) (x : GeometricPoint X)
    (p₀ : (finiteEtaleFiberFunctor x).obj T₁.cover) (σ : EtaleFundamentalGroup X x) :
    T₁.character x p₀ σ = T₂.character x ((finiteEtaleFiberFunctor x).map h p₀) σ := by
  apply Multiplicative.toAdd.injective
  refine (T₂.character_eq_of_smul x _ σ ((finiteEtaleFiberFunctor x).map h p₀) ?_).symm
  have hσ : σ • (finiteEtaleFiberFunctor x).map h p₀ = (finiteEtaleFiberFunctor x).map h (σ • p₀) :=
    (ConcreteCategory.congr_hom (σ.asIso.hom.naturality h) p₀)
  rw [hσ, T₁.smul_eq_character x p₀ σ p₀, ← ConcreteCategory.comp_apply, ← Functor.map_comp, hh,
    Functor.map_comp, ConcreteCategory.comp_apply]

variable [ConnectedSpace X] [ConnectedSpace Y]

/-- **The character of the base change is the character composed with `f_*`.** -/
public theorem baseChange_character (y : GeometricPoint Y)
    (p₀ : (finiteEtaleFiberFunctor y).obj (T.baseChange f).cover)
    (σ : EtaleFundamentalGroup Y y) :
    (T.baseChange f).character y p₀ σ =
      T.character (y.map f) (finiteEtaleFiberProjection f y T.cover p₀)
        (etaleFundamentalGroupMap f y σ) := by
  apply Multiplicative.toAdd.injective
  refine (T.character_eq_of_smul (y.map f) _ (etaleFundamentalGroupMap f y σ)
    (finiteEtaleFiberProjection f y T.cover p₀) ?_).symm
  have h1 := etaleFundamentalGroupMap_finiteEtaleFiberProjection f y T.cover σ p₀
  have h2 := (T.baseChange f).smul_eq_character y p₀ σ p₀
  refine h1.symm.trans ?_
  refine (congrArg (finiteEtaleFiberProjection f y T.cover) h2).trans ?_
  exact finiteEtaleFiberProjection_map_τ T f y _ p₀

end TorsorCover

end AlgebraicGeometry
