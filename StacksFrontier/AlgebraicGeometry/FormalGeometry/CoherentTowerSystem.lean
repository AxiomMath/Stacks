module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksCore.Tactic.StacksAttribute

/-!
# Systems of coherent modules along a tower of schemes

Let `X` be a scheme and let `Xₙ` be a tower of schemes over it: morphisms `iₙ : Xₙ ⟶ Xₙ₊₁` and
`kₙ : Xₙ ⟶ X` with `iₙ ≫ kₙ₊₁ = kₙ`. A *system of coherent modules along the tower* is a coherent
`𝒪_{Xₙ}`-module `ℱₙ` for every `n` together with an isomorphism `iₙ^* ℱₙ₊₁ ≅ ℱₙ`; these form a
category, and restricting a coherent `𝒪_X`-module along the `kₙ` is a functor into it.

This is the shape in which the conclusion of Grothendieck's algebraization theorem
([Stacks, Tag 089A]) asks for its invertible module: the compatibility the theorem demands between
the isomorphisms `ℒₙ ≅ ℒ|_{Xₙ}` and the transition isomorphisms `φₙ` is, verbatim, the statement
that the family `(ℒₙ ≅ ℒ|_{Xₙ})` is a morphism in the category below.

## Main definitions

* `Stacks.CoherentTower.ModuleSystem` — the systems `(ℱₙ, φₙ)` along the tower, with
  `ModuleSystem.Hom` and the resulting category.
* `Stacks.CoherentTower.restrictionNatIso` — the natural isomorphism
  `iₙ^*(kₙ₊₁^* -) ≅ kₙ^* -` furnished by `iₙ ≫ kₙ₊₁ = kₙ`.
* `Stacks.CoherentTower.restriction` — the restriction functor from coherent `𝒪_X`-modules to
  systems along the tower.

## Main results

* `Stacks.CoherentTower.ModuleSystem.isoApp` — an isomorphism of systems is an isomorphism in
  every degree.
* `Stacks.CoherentTower.transitionIso_restriction` — the transition isomorphism of a restricted
  module, written out as the composite of `Scheme.Modules.pullbackComp` and
  `Scheme.Modules.pullbackCongr` that [Stacks, Tag 089A] states its compatibility clause with.

## Implementation notes

`AlgebraicGeometry.AdicCoherentModuleSystem` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningCoherentSystem.lean` is the special
case of `ModuleSystem` at the canonical tower `Xₙ = X ×_S Sₙ`, `kₙ = pullback.fst`. The general
form is needed because the tower of [Stacks, Tag 089A] is not that tower but only cartesian over
the same base: the theorem's `Xₙ` carry an *abstract* morphism `kₙ : Xₙ ⟶ X` exhibiting them as
fibre products, and transporting the whole system along the comparison isomorphisms is exactly
what the general statement avoids.

Only `iₙ` enters the objects; the morphisms `kₙ` and the identities `iₙ ≫ kₙ₊₁ = kₙ` enter only
the restriction functor. Coherence of a restricted module is Stacks 0EBF
(`AlgebraicGeometry.isCoherent_pullback`), which needs each `Xₙ` locally Noetherian and nothing
else.

Coherence is spelled `_root_.SheafOfModules.IsCoherent.{u}`: the predicate is declared more than
once and a relative spelling can resolve to `Stacks.SheafOfModules.IsCoherent`, a different
constant.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CoherentTower

variable {X : Scheme.{u}} {Xn : ℕ → Scheme.{u}}

/-! ### The systems -/

/-- **A system of coherent modules along a tower `iₙ : Xₙ ⟶ Xₙ₊₁`.** A coherent
`𝒪_{Xₙ}`-module for every `n`, together with an isomorphism `iₙ^* ℱₙ₊₁ ≅ ℱₙ`.

The transition isomorphism is *data*, as in [Stacks, Tag 089A] and [Stacks, Tag 088F], not merely
an existence statement: it is part of the system. -/
public structure ModuleSystem (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1)) where
  /-- The sheaf of modules on the `n`-th member of the tower. -/
  obj (n : ℕ) : (Xn n).Modules
  /-- Every term is coherent. -/
  isCoherent (n : ℕ) : _root_.SheafOfModules.IsCoherent.{u} (obj n)
  /-- The transition isomorphism `φₙ : iₙ^* ℱₙ₊₁ ≅ ℱₙ`. -/
  transitionIso (n : ℕ) : (Scheme.Modules.pullback (i n)).obj (obj (n + 1)) ≅ obj n

namespace ModuleSystem

variable {i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1)}

/-- A morphism of systems: a map of sheaves of modules on every member of the tower, compatible
with the transition isomorphisms. -/
@[ext]
public structure Hom (F G : ModuleSystem i) where
  /-- The component on the `n`-th member of the tower. -/
  app (n : ℕ) : F.obj n ⟶ G.obj n
  /-- Compatibility with the transition isomorphisms. -/
  comm (n : ℕ) :
    (Scheme.Modules.pullback (i n)).map (app (n + 1)) ≫ (G.transitionIso n).hom =
      (F.transitionIso n).hom ≫ app n

/-- The category of systems along the tower: composition and identities are computed
degreewise. -/
public instance : Category (ModuleSystem i) where
  Hom F G := Hom F G
  id F :=
    { app := fun _ => 𝟙 _
      comm := fun n => by simp }
  comp {F G H} α β :=
    { app := fun n => α.app n ≫ β.app n
      comm := fun n => by
        rw [Functor.map_comp, Category.assoc, β.comm n, ← Category.assoc, α.comm n,
          Category.assoc] }
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)

/-- **An isomorphism of systems is an isomorphism in every degree.** Composition and identities
are computed degreewise, so the two triangle identities hold degreewise. -/
public def isoApp {F G : ModuleSystem i} (e : F ≅ G) (n : ℕ) : F.obj n ≅ G.obj n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := by
    have h : (e.hom ≫ e.inv).app n = (𝟙 F : F ⟶ F).app n := by rw [e.hom_inv_id]
    exact h
  inv_hom_id := by
    have h : (e.inv ≫ e.hom).app n = (𝟙 G : G ⟶ G).app n := by rw [e.inv_hom_id]
    exact h

/-- The forward map of `isoApp e n` is the `n`-th component of `e.hom`. -/
@[simp]
public lemma isoApp_hom {F G : ModuleSystem i} (e : F ≅ G) (n : ℕ) :
    (isoApp e n).hom = e.hom.app n := rfl

end ModuleSystem

/-! ### Restriction along the tower -/

variable (i : ∀ n : ℕ, Xn n ⟶ Xn (n + 1)) (k : ∀ n : ℕ, Xn n ⟶ X)

/-- **The transition isomorphism of a restricted module, as a natural isomorphism of functors.**
Since `kₙ = iₙ ≫ kₙ₊₁`, pulling back along `kₙ₊₁` and then along `iₙ` is pulling back along
`kₙ`. -/
public def restrictionNatIso (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n) (n : ℕ) :
    Scheme.Modules.pullback (k (n + 1)) ⋙ Scheme.Modules.pullback (i n) ≅
      Scheme.Modules.pullback (k n) :=
  Scheme.Modules.pullbackComp (i n) (k (n + 1)) ≪≫ Scheme.Modules.pullbackCongr (hk n)

/-- **Restriction of a coherent `𝒪_X`-module along the tower.** It sends `ℱ` to the system
`(ℱ|_{Xₙ})` of its pullbacks along the `kₙ`, with the transition isomorphisms induced by
`iₙ ≫ kₙ₊₁ = kₙ`.

Coherence of each term is Stacks 0EBF; nothing else about the tower is used. -/
public def restriction [∀ n : ℕ, IsLocallyNoetherian (Xn n)]
    (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤ ModuleSystem i where
  obj F :=
    { obj := fun n => (Scheme.Modules.pullback (k n)).obj F.obj
      isCoherent := fun n => isCoherent_pullback (k n) F.obj
      transitionIso := fun n => (restrictionNatIso i k hk n).app F.obj }
  map φ :=
    { app := fun n => (Scheme.Modules.pullback (k n)).map φ.hom
      comm := fun n => (restrictionNatIso i k hk n).hom.naturality φ.hom }
  map_id _ := ModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_id _ _)
  map_comp _ _ := ModuleSystem.Hom.ext (funext fun _ => CategoryTheory.Functor.map_comp _ _ _)

/-- **The transition isomorphism of a restricted module, written out.** This is the composite of
`Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr` in which the compatibility
clause of [Stacks, Tag 089A] is phrased. -/
public lemma transitionIso_restriction [∀ n : ℕ, IsLocallyNoetherian (Xn n)]
    (hk : ∀ n : ℕ, i n ≫ k (n + 1) = k n)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    (((restriction i k hk).obj F).transitionIso n).hom =
      (Scheme.Modules.pullbackComp (i n) (k (n + 1))).hom.app F.obj ≫
        (Scheme.Modules.pullbackCongr (hk n)).hom.app F.obj :=
  rfl

end Stacks.CoherentTower

end
