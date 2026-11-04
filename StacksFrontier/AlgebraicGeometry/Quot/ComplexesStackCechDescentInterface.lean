module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizes
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleRingedToposHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineKFlatModel

/-!
# Stacks 0DLA, Čech case: the interface of its pieces

`AlgebraicGeometry.Space.ComplexesSituation.CechDescent` is Stacks 0DLA for the Čech hypercovering
of an fppf covering, read on the small étale sites with modules in `Type u`. The source's proof is
0GMF (a pair `(K₀, α)` gives a cartesian simplicial system), 0D9T (that system comes from a
cartesian object of `D(𝒪_U)`) and 0DHF (that object is `La^*K`). The base's 0D9T,
`CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`, asks for
flat transitions `f_φ^{-1}𝒪_n ⟶ 𝒪_m` along *every* simplex map; for an fppf hypercovering the
degeneracies are diagonals and are not flat, so it does not apply. The source never checks it.

This file fixes the statements of the pieces that replace that step, as propositions, and proves
that together they give `CechDescent` (`cechDescent_of_pieces`). Nothing here is registered and no
piece is proved here.

## The pieces

* **P-core** `CategoryTheory.SimplicialSiteSituation.CartesianModuleSystemRealizes`: Stacks 0D9T
  without the flatness hypothesis, in every simplicial-site situation (Stacks 09WE). The base's
  0D9T is this statement plus `hflat`
  (`CategoryTheory.SimplicialSiteSituation.cartesianModuleSystemRealizes_of_isFlat` checks the
  shape). The route is to rebuild `Lg_{n!}` from K-flat resolutions: `g_{n!}` carries K-flat
  complexes with flat terms to complexes whose restriction to degree `m` is
  `⨁_{φ : [n] ⟶ [m]} f_φ^*P`, which computes `⨁_φ Lf_φ^*P` with no flatness assumption.
* **P-0DHF** `AlgebraicGeometry.Space.SpacesEtaleHypercoverDescentOfRealization`: from P-core,
  Stacks 0DLA on the spaces-étale sites (modules in `Type (u + 1)`), where the base's 0DHF
  (`SimplicialSpacesEtaleSite.isWeakSerreClass_and_derivedPullback_equivalence` in
  `AlgebraicGeometry.Space`) lives. It runs 0GMF and P-core on the simplicial-site situation of
  the strict components
  (`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictSituation`) and then 0DHF.
* **P-univ** `AlgebraicGeometry.Space.SmallEtaleSpacesEtaleDescentComparison` (the comparison of
  the small étale and the spaces-étale derived categories, on quasi-coherent complexes and along
  fppf coverings) and `AlgebraicGeometry.Space.SmallEtaleHypercoverDescentOfSpacesEtale` (with it,
  0DLA moves from the spaces-étale to the small étale sites).
* **P-cech** `AlgebraicGeometry.Space.CechDescentOfSmallEtaleHypercoverDescent`: from 0DLA on the
  small étale sites, `CechDescent`. This is a u-small refinement of the covering, its Čech nerve
  as an fppf hypercovering, the input `(K₀, α)` and its cocycle condition, and the translation of
  the output into the `ψ i` and `FibresCompatible` for all pairs `(i, j)`.

## The 0DLA shape

`CategoryTheory.HypercoverDerivedDescent` is Stacks 0DLA for an arbitrary contravariant assignment
`pull` of functors with a composition comparison `comp`, a class `H` of augmented simplicial
objects (the hypercoverings) and a property `Q` of objects (quasi-coherent cohomology). Given an
object `H`, `K₀` over `U₀` with an isomorphism `α : δ₁^*K₀ ≅ δ₀^*K₀` satisfying the cocycle
condition on `U₂` (`CategoryTheory.IsHypercoverDescentCocycle`), with `Q K₀` and
`Ext^t(K_n, K_n) = 0` for `t < 0`, where `K_n` is the pullback of `K₀` along the last vertex
`τⁿₙ : [0] ⟶ [n]`, there is `K` over the base with `Q K` and an isomorphism `β : a₀^*K ≅ K₀`
compatible with `α` (`CategoryTheory.IsHypercoverDescentCompatible`). It is the source's 0DLA, with
no uniqueness clause.

Wherever a pullback along a morphism that is only *equal* to a composite occurs, the equality is a
hypothesis of the statement (`CategoryTheory.hypercoverPullTriangle`), so that no proof term of a
simplicial identity is part of a statement.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### The 0DLA shape, for a pullback assignment with a composition comparison -/

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

/-- The pullback along a morphism `k` equal to a composite `f ≫ g`, compared with the composite of
the pullbacks: `comp f g` after the identification of `pull k` with `pull (f ≫ g)`. -/
def hypercoverPullTriangle {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k) :
    pull k ≅ pull g ⋙ pull f :=
  eqToIso (congrArg (fun m : a ⟶ c => pull m) hk.symm) ≪≫ comp f g

/-- The restriction of a gluing map `α : s^*K₀ ⟶ t^*K₀` along `e : Z ⟶ U₁`, read between the
pullbacks of `K₀` along `v = e ≫ s` and `w = e ≫ t`. -/
def hypercoverEdgeRestrict {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {U₀ U₁ : A} {s t : U₁ ⟶ U₀} {K₀ : D U₀} (α : (pull s).obj K₀ ⟶ (pull t).obj K₀) {Z : A}
    (e : Z ⟶ U₁) {v w : Z ⟶ U₀} (hv : e ≫ s = v) (hw : e ≫ t = w) :
    (pull v).obj K₀ ⟶ (pull w).obj K₀ :=
  (hypercoverPullTriangle pull comp hv).hom.app K₀ ≫ (pull e).map α ≫
    (hypercoverPullTriangle pull comp hw).inv.app K₀

/-- **The cocycle condition of Stacks 0GMF / 0DLA.** For the two vertex maps `s = δ₁`, `t = δ₀`
from `U₁` to `U₀` and the three edge maps `e₀₁ = δ₂`, `e₁₂ = δ₀`, `e₀₂ = δ₁` from `U₂` to `U₁`, the
restrictions of `α` along the edges compose: `α|_{01} ≫ α|_{12} = α|_{02}` as maps from the
pullback of `K₀` along the vertex `0` of `U₂` to that along the vertex `2`. The three vertices
`v₀`, `v₁`, `v₂` of `U₂` are arguments, each with its two presentations as a composite. -/
def IsHypercoverDescentCocycle {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {U₀ U₁ U₂ : A} (s t : U₁ ⟶ U₀) (e₀₁ e₁₂ e₀₂ : U₂ ⟶ U₁) {K₀ : D U₀}
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀) : Prop :=
  ∀ (v₀ v₁ v₂ : U₂ ⟶ U₀) (h₀ : e₀₁ ≫ s = v₀) (h₁ : e₀₁ ≫ t = v₁) (h₁' : e₁₂ ≫ s = v₁)
    (h₂ : e₁₂ ≫ t = v₂) (h₀' : e₀₂ ≫ s = v₀) (h₂' : e₀₂ ≫ t = v₂),
    hypercoverEdgeRestrict pull comp α.hom e₀₁ h₀ h₁ ≫
        hypercoverEdgeRestrict pull comp α.hom e₁₂ h₁' h₂ =
      hypercoverEdgeRestrict pull comp α.hom e₀₂ h₀' h₂'

/-- **Compatibility of `β : a₀^*K ≅ K₀` with `α`** (Stacks 0DLA): through `β`, the gluing map
`α : s^*K₀ ≅ t^*K₀` is the canonical identification `s^*a₀^*K ≅ a₁^*K ≅ t^*a₀^*K`, for the
augmentation `a₁ = s ≫ a₀ = t ≫ a₀` of `U₁`. -/
def IsHypercoverDescentCompatible {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {X U₀ U₁ : A} (a₀ : U₀ ⟶ X) (s t : U₁ ⟶ U₀) {K₀ : D U₀}
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀) (K : D X) (β : (pull a₀).obj K ≅ K₀) : Prop :=
  ∀ (a₁ : U₁ ⟶ X) (hs : s ≫ a₀ = a₁) (ht : t ≫ a₀ = a₁),
    (pull s).map β.inv ≫ (hypercoverPullTriangle pull comp hs).inv.app K ≫
        (hypercoverPullTriangle pull comp ht).hom.app K ≫ (pull t).map β.hom = α.hom

/-- **The shape of Stacks 0DLA.** For every augmented simplicial object `U ⟶ X` in the class `H`,
every `K₀` over `U₀` with `Q K₀` and every `α : δ₁^*K₀ ≅ δ₀^*K₀` satisfying the cocycle condition
on `U₂`, such that `Ext^t(K_n, K_n) = 0` for `t < 0` where `K_n = (τⁿₙ)^*K₀` is the pullback along
the last vertex `τⁿₙ : [0] ⟶ [n]`, there are `K` over `X` with `Q K` and an isomorphism
`β : a₀^*K ≅ K₀` compatible with `α`. -/
def HypercoverDerivedDescent {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] [∀ a, HasShift (D a) ℤ]
    (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    (H : SimplicialObject.Augmented A → Prop) (Q : ∀ a : A, D a → Prop) : Prop :=
  ∀ (U : SimplicialObject.Augmented A), H U →
    ∀ (K₀ : D (U.left.obj (op (SimplexCategory.mk 0))))
      (α : (pull (U.left.δ (1 : Fin 2))).obj K₀ ≅ (pull (U.left.δ (0 : Fin 2))).obj K₀),
      IsHypercoverDescentCocycle pull comp (U.left.δ (1 : Fin 2)) (U.left.δ (0 : Fin 2))
        (U.left.δ (2 : Fin 3)) (U.left.δ (0 : Fin 3)) (U.left.δ (1 : Fin 3)) α →
      Q _ K₀ →
      (∀ (n : ℕ) (t : ℤ), t < 0 →
        Subsingleton ((pull (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) (Fin.last n)).op)).obj K₀ ⟶
          ((pull (U.left.map (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) (Fin.last n)).op)).obj K₀)⟦t⟧)) →
      ∃ (K : D U.right) (β : (pull (U.hom.app (op (SimplexCategory.mk 0)))).obj K ≅ K₀),
        Q U.right K ∧
          IsHypercoverDescentCompatible pull comp (U.hom.app (op (SimplexCategory.mk 0)))
            (U.left.δ (1 : Fin 2)) (U.left.δ (0 : Fin 2)) α K β

end CategoryTheory

/-! ### 0DLA on the small étale and on the spaces-étale sites -/

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering
open AlgebraicGeometry.Space.SimplicialSpacesEtaleSite (spacesEtaleRingedToposHom)

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory
  HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A complex on the small étale site of `X` (modules in `Type u`) has quasi-coherent cohomology
sheaves. At `X = D.space T` this is
`AlgebraicGeometry.Space.ComplexesSituation.HasQuasicoherentCohomology`. -/
def IsSmallEtaleQuasicoherentComplex (X : AlgebraicSpaces B S hS) (E : derivedModules B S hS X) :
    Prop :=
  ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
    E).IsQuasicoherentOnSite

/-- The derived category of modules on the spaces-étale site of `X`, with sections in
`Type (u + 1)`: the category Stacks 0DHF is proved on. -/
abbrev spacesEtaleDerivedModules (X : AlgebraicSpaces B S hS) :=
  @DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) _ _
    (HasDerivedCategory.standard _)

/-- A complex on the spaces-étale site of `X` has quasi-coherent cohomology sheaves, in the form
Stacks 0DHF is stated with. -/
def IsSpacesEtaleQuasicoherentComplex (X : AlgebraicSpaces B S hS)
    (E : spacesEtaleDerivedModules B S hS X) : Prop :=
  (@DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O))) E

/-- The derived pullback along a morphism of algebraic spaces on the spaces-étale sites. -/
abbrev spacesEtaleDerivedPull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    spacesEtaleDerivedModules B S hS Y ⥤ spacesEtaleDerivedModules B S hS X :=
  derivedPullback (X := spacesEtaleRingedTopos B S hS X) (Y := spacesEtaleRingedTopos B S hS Y)
    (spacesEtaleRingedToposHom f)

/-- Stacks 0D6D on the spaces-étale sites, `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`. -/
abbrev spacesEtaleDerivedPullComp {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleDerivedPull B S hS (f ≫ g) ≅
      spacesEtaleDerivedPull B S hS g ⋙ spacesEtaleDerivedPull B S hS f :=
  (spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp f g).symm

/-- **Stacks 0DLA on the small étale sites** (internal; the output of P-univ, the input of
P-cech). Let `a : U ⟶ X` be an fppf hypercovering of algebraic spaces over `S`
(`AlgebraicGeometry.Space.fppfCoveringMorphisms`). Suppose given `K₀ ∈ D_QCoh(𝒪_{U₀})` and an
isomorphism `α : Lδ₁^*K₀ ⟶ Lδ₀^*K₀` satisfying the cocycle condition on `U₂`, and assume
`Ext^t(K_n, K_n) = 0` for `t < 0`, where `K_n = Lτⁿₙ^*K₀`. Then there exist `K ∈ D_QCoh(𝒪_X)` and
an isomorphism `La₀^*K ⟶ K₀` compatible with `α`. Derived pullbacks are those of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, with modules in `Type u`. -/
def SmallEtaleHypercoverDescent : Prop :=
  @HypercoverDerivedDescent (AlgebraicSpaces B S hS) _ (derivedModules B S hS)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (smallEtaleDerivedPullbackData B S hS).pull (smallEtaleDerivedPullbackData B S hS).compIso
    (fun U => (fppfCoveringMorphisms B S hS).IsHypercovering U)
    (IsSmallEtaleQuasicoherentComplex B S hS)

/-- **Stacks 0DLA on the spaces-étale sites** (internal; the output of P-0DHF). As
`AlgebraicGeometry.Space.SmallEtaleHypercoverDescent`, but on the spaces-étale sites with
modules in `Type (u + 1)`, for a hypercovering augmentation of the big fppf site of algebraic
spaces `AlgebraicGeometry.Space.bigFppfSpaceSiteOfSchemeSite`: the setting of the base's Stacks
0DHF. -/
def SpacesEtaleHypercoverDescent : Prop :=
  @HypercoverDerivedDescent (AlgebraicSpaces B S hS) _ (spacesEtaleDerivedModules B S hS)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun f => spacesEtaleDerivedPull B S hS f) (fun f g => spacesEtaleDerivedPullComp B S hS f g)
    (fun U => IsHypercoveringAugmentation
      (bigFppfSpaceSiteOfSchemeSite B S hS).pretopologyBigFppfPretopology U.left U.hom)
    (IsSpacesEtaleQuasicoherentComplex B S hS)

/-- **Piece P-0DHF** (internal, pending): Stacks 0D9T without flatness (P-core, at the universe
`u + 1` of the spaces-étale sites) gives Stacks 0DLA on the spaces-étale sites. The source's proof:
0GMF turns `(K₀, α)` into a cartesian simplicial system on the simplicial-site situation of the
strict components of `U`, P-core realizes it as a cartesian object of `D(𝒪_U)`, and 0DHF writes
that object as `La^*K`. -/
def SpacesEtaleHypercoverDescentOfRealization : Prop :=
  (∀ (C : CategoryTheory.SimplicialSiteSituation.{u + 1})
      (O : Sheaf C.totalTopology CommRingCat.{u + 1}), C.CartesianModuleSystemRealizes O) →
    SpacesEtaleHypercoverDescent B S hS

/-- **Piece P-univ, the comparison** (internal, pending): functors
`Φ_X : D(𝒪_X) ⥤ D(𝒪_{X, spaces-étale})`, from modules on the small étale site of `X` with
sections in `Type u` to modules on the spaces-étale site with sections in `Type (u + 1)`, and
isomorphisms `ε_f : Lf^* ⋙ Φ_X ≅ Φ_Y ⋙ Lf^*` for the fppf coverings `f : X ⟶ Y`, such that

1. `Φ_X` is bijective on morphisms between complexes with quasi-coherent cohomology;
2. `Φ_X(K⟦i⟧) ≅ Φ_X(K)⟦i⟧`;
3. `Φ_X` carries complexes with quasi-coherent cohomology to such complexes;
4. its essential image descends along fppf coverings: if `L ∈ D_QCoh(𝒪_{X, spaces-étale})` and
   `Lf^*L ≅ Φ_Y(K')` for an fppf covering `f : Y ⟶ X` and `K' ∈ D_QCoh(𝒪_Y)`, then `L ≅ Φ_X(K)`
   for some `K ∈ D_QCoh(𝒪_X)`;
5. the `ε` are compatible with the composition comparisons of Stacks 0D6D on both sides.

The `ε` are asked only along fppf coverings: every pullback that 0DLA uses is along a face, a
vertex or an augmentation map of an fppf hypercovering, all fppf coverings, along which both
derived pullbacks are underived. -/
def SmallEtaleSpacesEtaleDescentComparison : Prop :=
  ∃ (Φ : ∀ X : AlgebraicSpaces B S hS, derivedModules B S hS X ⥤ spacesEtaleDerivedModules B S hS X)
    (ε : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), fppfCoveringMorphisms B S hS f →
      ((smallEtaleDerivedPullbackData B S hS).pull f ⋙ Φ X ≅
        Φ Y ⋙ spacesEtaleDerivedPull B S hS f)),
    (∀ (X : AlgebraicSpaces B S hS) (K E : derivedModules B S hS X),
      IsSmallEtaleQuasicoherentComplex B S hS X K → IsSmallEtaleQuasicoherentComplex B S hS X E →
        Function.Bijective (fun g : K ⟶ E => (Φ X).map g)) ∧
    (∀ (X : AlgebraicSpaces B S hS) (K : derivedModules B S hS X) (i : ℤ),
      Nonempty ((Φ X).obj (K⟦i⟧) ≅ ((Φ X).obj K)⟦i⟧)) ∧
    (∀ (X : AlgebraicSpaces B S hS) (K : derivedModules B S hS X),
      IsSmallEtaleQuasicoherentComplex B S hS X K →
        IsSpacesEtaleQuasicoherentComplex B S hS X ((Φ X).obj K)) ∧
    (∀ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X), fppfCoveringMorphisms B S hS f →
      ∀ (L : spacesEtaleDerivedModules B S hS X), IsSpacesEtaleQuasicoherentComplex B S hS X L →
      ∀ (K' : derivedModules B S hS Y), IsSmallEtaleQuasicoherentComplex B S hS Y K' →
      Nonempty ((Φ Y).obj K' ≅ (spacesEtaleDerivedPull B S hS f).obj L) →
      ∃ K : derivedModules B S hS X, IsSmallEtaleQuasicoherentComplex B S hS X K ∧
        Nonempty ((Φ X).obj K ≅ L)) ∧
    ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
      (hf : fppfCoveringMorphisms B S hS f) (hg : fppfCoveringMorphisms B S hS g)
      (hfg : fppfCoveringMorphisms B S hS (f ≫ g)) (K : derivedModules B S hS Z),
      (ε (f ≫ g) hfg).hom.app K ≫ (spacesEtaleDerivedPullComp B S hS f g).hom.app ((Φ Z).obj K) =
        (Φ X).map (((smallEtaleDerivedPullbackData B S hS).compIso f g).hom.app K) ≫
          (ε f hf).hom.app (((smallEtaleDerivedPullbackData B S hS).pull g).obj K) ≫
            (spacesEtaleDerivedPull B S hS f).map ((ε g hg).hom.app K)

/-- **Piece P-univ, the transfer** (internal, pending): with the comparison, Stacks 0DLA on the
spaces-étale sites gives Stacks 0DLA on the small étale sites. -/
def SmallEtaleHypercoverDescentOfSpacesEtale : Prop :=
  SmallEtaleSpacesEtaleDescentComparison B S hS → SpacesEtaleHypercoverDescent B S hS →
    SmallEtaleHypercoverDescent B S hS

/-- **Piece P-cech** (internal, pending): Stacks 0DLA on the small étale sites gives its Čech case
`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`. The proof refines the covering to a
u-small one, takes the Čech nerve of `∐ X_{T_k} ⟶ X_T` as an fppf hypercovering, builds `K₀` and
`α` from the Čech data, and translates the output into the `ψ i` and `FibresCompatible` for all
pairs `(i, j)` (morphisms descend by 0DLC(3)/0DLG). -/
def CechDescentOfSmallEtaleHypercoverDescent : Prop :=
  SmallEtaleHypercoverDescent B S hS → ∀ D : ComplexesSituation B S hS, D.CechDescent

variable {B S hS} in
/-- **Stacks 0DLA, Čech case, from its pieces.** P-core (at the universe `u + 1`), P-0DHF, P-univ
and P-cech give `CechDescent` for every `Complexes` situation over `S`. -/
theorem ComplexesSituation.cechDescent_of_pieces
    (hcore : ∀ (C : CategoryTheory.SimplicialSiteSituation.{u + 1})
      (O : Sheaf C.totalTopology CommRingCat.{u + 1}), C.CartesianModuleSystemRealizes O)
    (h0DHF : SpacesEtaleHypercoverDescentOfRealization B S hS)
    (hcomp : SmallEtaleSpacesEtaleDescentComparison B S hS)
    (huniv : SmallEtaleHypercoverDescentOfSpacesEtale B S hS)
    (hcech : CechDescentOfSmallEtaleHypercoverDescent B S hS)
    (D : ComplexesSituation B S hS) : D.CechDescent :=
  hcech (huniv hcomp (h0DHF hcore)) D

/-- **Stacks 0DLA, Čech case, from its pieces, for every base**: the shape of the hypothesis
`h0DLA` of `AlgebraicGeometry.Space.isAlgebraicStack_complexes_of_external`. -/
theorem ComplexesSituation.cechDescent_of_pieces_all
    (hcore : ∀ (C : CategoryTheory.SimplicialSiteSituation.{u + 1})
      (O : Sheaf C.totalTopology CommRingCat.{u + 1}), C.CartesianModuleSystemRealizes O)
    (h0DHF : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      SpacesEtaleHypercoverDescentOfRealization B S hS)
    (hcomp : ∀ {S : Scheme.{u}} (hS : B.Contains S), SmallEtaleSpacesEtaleDescentComparison B S hS)
    (huniv : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      SmallEtaleHypercoverDescentOfSpacesEtale B S hS)
    (hcech : ∀ {S : Scheme.{u}} (hS : B.Contains S),
      CechDescentOfSmallEtaleHypercoverDescent B S hS) :
    ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS), D.CechDescent :=
  fun hS D => cechDescent_of_pieces hcore (h0DHF hS) (hcomp hS) (huniv hS) (hcech hS) D

end AlgebraicGeometry.Space

end
