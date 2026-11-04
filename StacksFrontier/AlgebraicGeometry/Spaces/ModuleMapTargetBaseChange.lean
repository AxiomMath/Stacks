module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
import all StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback

/-!
# Base change of the standing situation along a morphism of the target space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`u : F ⟶ G` be a map of quasi-coherent `𝒪_X`-modules, so that `(X, Y, f, F, G, u)` is the
standing datum of Stacks 083F.  A morphism `b : Y' ⟶ Y` of algebraic spaces turns this datum
into a datum over `Y'`: the source becomes `X ×_Y Y'`, the structure morphism the second
projection, and the two modules and the map between them their inverse images along the first
projection `X ×_Y Y' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTarget` is the base-changed standing
  datum over `Y'`; its two modules are quasi-coherent by Stacks 03GA.
* `AlgebraicGeometry.Space.ModuleMapSituation.overTarget` reads a test scheme over `Y'` as a
  test scheme over `Y`, by composing its structure morphism with `b`.
* `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTargetSpaceIso` is the comparison
  `(X ×_Y Y') ×_{Y'} T ≅ X ×_Y T` of the two base-change spaces at a test scheme `T` over `Y'`.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_baseChangeTarget_iff`,
  `.isSurjectiveAt_baseChangeTarget_iff` and `.isIsoAt_baseChangeTarget_iff`: at a test scheme
  `T` over `Y'`, the base-changed situation satisfies the condition exactly when the original
  situation satisfies it at `T` read over `Y`.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroFunctorBaseChangeTargetIso`,
  `.surjFunctorBaseChangeTargetIso` and `.isoFunctorBaseChangeTargetIso`: the three subterminal
  functors of Stacks 083F of the base-changed situation are the restrictions along `overTarget`
  of those of the original.
* `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeTargetSpaceIdIso` and
  `.baseChangeTargetSpaceCompIso`: the identity and composition laws, as isomorphisms of the
  source spaces compatible with the projections to `X`.

## Implementation notes

The three comparisons of conditions are proved over an arbitrary
`AlgebraicGeometry.Space.ModulePullbackSystem` whose functors are
`AlgebraicGeometry.Space.modulePullback` (the `_of` lemmas), and then instantiated at
`AlgebraicGeometry.Space.modulePullbackSystem`, so that elaboration never unfolds the concrete
system.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Pullback along a composite and along an isomorphism, condition by condition -/

namespace ModulePullbackSystem

variable (P : ModulePullbackSystem.{u, u} B S hS)

section Comp

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (a : M ⟶ N)

/-- The pullback of a map of modules along a composite vanishes exactly when the iterated
pullback does. -/
theorem map_comp_eq_zero_iff :
    (P.functor (f ≫ g)).map a = 0 ↔ (P.functor f).map ((P.functor g).map a) = 0 := by
  rw [P.map_comp_eq_conj f g a, eq_zero_conj_iff]

/-- The pullback of a map of modules along a composite is an epimorphism exactly when the
iterated pullback is. -/
theorem epi_map_comp_iff :
    Epi ((P.functor (f ≫ g)).map a) ↔ Epi ((P.functor f).map ((P.functor g).map a)) := by
  rw [P.map_comp_eq_conj f g a, epi_conj_iff]

/-- The pullback of a map of modules along a composite is an isomorphism exactly when the
iterated pullback is. -/
theorem isIso_map_comp_iff :
    IsIso ((P.functor (f ≫ g)).map a) ↔ IsIso ((P.functor f).map ((P.functor g).map a)) := by
  rw [P.map_comp_eq_conj f g a, isIso_conj_iff]

end Comp

section Precompose

variable {A A' X : AlgebraicSpaces B S hS} (c : A ⟶ A') (w : A' ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2} (a : M ⟶ N)

/-- A vanishing pullback stays vanishing after precomposing with a further morphism. -/
theorem map_comp_eq_zero (h : (P.functor w).map a = 0) : (P.functor (c ≫ w)).map a = 0 := by
  have := P.preservesZeroMorphisms c
  rw [P.map_comp_eq_zero_iff c w a, h]
  simp

/-- A surjective pullback stays surjective after precomposing with a further morphism. -/
theorem epi_map_comp (h : Epi ((P.functor w).map a)) : Epi ((P.functor (c ≫ w)).map a) := by
  have := h
  rw [P.epi_map_comp_iff c w a]
  exact (P.preservesEpimorphisms c).preserves _

/-- A pullback that is an isomorphism stays one after precomposing with a further morphism. -/
theorem isIso_map_comp (h : IsIso ((P.functor w).map a)) : IsIso ((P.functor (c ≫ w)).map a) := by
  have := h
  rw [P.isIso_map_comp_iff c w a]
  exact Functor.map_isIso (P.functor c) ((P.functor w).map a)

/-- Pullback along equal morphisms gives the same vanishing condition. -/
theorem map_eq_zero_congr {A X : AlgebraicSpaces B S hS} {w w' : A ⟶ X} (hw : w = w')
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    (P.functor w).map v = 0 ↔ (P.functor w').map v = 0 := by
  subst hw
  exact Iff.rfl

/-- Pullback along equal morphisms gives the same surjectivity condition. -/
theorem epi_map_congr {A X : AlgebraicSpaces B S hS} {w w' : A ⟶ X} (hw : w = w')
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    Epi ((P.functor w).map v) ↔ Epi ((P.functor w').map v) := by
  subst hw
  exact Iff.rfl

/-- Pullback along equal morphisms gives the same isomorphism condition. -/
theorem isIso_map_congr {A X : AlgebraicSpaces B S hS} {w w' : A ⟶ X} (hw : w = w')
    {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N) :
    IsIso ((P.functor w).map v) ↔ IsIso ((P.functor w').map v) := by
  subst hw
  exact Iff.rfl

variable [IsIso c]

/-- Precomposing the morphism along which one pulls back with an isomorphism does not change
whether the pullback of a map of modules vanishes. -/
theorem map_eq_zero_isIso_comp_iff :
    (P.functor (c ≫ w)).map a = 0 ↔ (P.functor w).map a = 0 := by
  refine ⟨fun h => ?_, P.map_comp_eq_zero c w a⟩
  have key := P.map_comp_eq_zero (inv c) (c ≫ w) a h
  rwa [IsIso.inv_hom_id_assoc] at key

/-- Precomposing the morphism along which one pulls back with an isomorphism does not change
whether the pullback of a map of modules is an epimorphism. -/
theorem epi_map_isIso_comp_iff :
    Epi ((P.functor (c ≫ w)).map a) ↔ Epi ((P.functor w).map a) := by
  refine ⟨fun h => ?_, P.epi_map_comp c w a⟩
  have key := P.epi_map_comp (inv c) (c ≫ w) a h
  rwa [IsIso.inv_hom_id_assoc] at key

/-- Precomposing the morphism along which one pulls back with an isomorphism does not change
whether the pullback of a map of modules is an isomorphism. -/
theorem isIso_map_isIso_comp_iff :
    IsIso ((P.functor (c ≫ w)).map a) ↔ IsIso ((P.functor w).map a) := by
  refine ⟨fun h => ?_, P.isIso_map_comp c w a⟩
  have key := P.isIso_map_comp (inv c) (c ≫ w) a h
  rwa [IsIso.inv_hom_id_assoc] at key

end Precompose

/-! ### An iterated pullback against a single one, across a comparison isomorphism -/

section Iterated

variable {A A' X Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS X.1 X.2}

/-- If the composite `A ⟶ A' ⟶ X` factors as an isomorphism `e : A ⟶ Z` followed by
`w : Z ⟶ X`, then pulling `v` back to `A'` and then to `A` gives zero exactly when pulling it
back along `w` does. -/
theorem map_eq_zero_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) {e : A ⟶ Z} (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    (P.functor c₁).map ((P.functor c₂).map v) = 0 ↔ (P.functor w).map v = 0 :=
  have := hiso
  (P.map_comp_eq_zero_iff c₁ c₂ v).symm.trans
    ((P.map_eq_zero_congr he v).trans (P.map_eq_zero_isIso_comp_iff e w v))

/-- If the composite `A ⟶ A' ⟶ X` factors as an isomorphism `e : A ⟶ Z` followed by
`w : Z ⟶ X`, then pulling `v` back to `A'` and then to `A` is an epimorphism exactly when
pulling it back along `w` is. -/
theorem epi_map_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) {e : A ⟶ Z} (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    Epi ((P.functor c₁).map ((P.functor c₂).map v)) ↔ Epi ((P.functor w).map v) :=
  have := hiso
  (P.epi_map_comp_iff c₁ c₂ v).symm.trans
    ((P.epi_map_congr he v).trans (P.epi_map_isIso_comp_iff e w v))

/-- If the composite `A ⟶ A' ⟶ X` factors as an isomorphism `e : A ⟶ Z` followed by
`w : Z ⟶ X`, then pulling `v` back to `A'` and then to `A` is an isomorphism exactly when
pulling it back along `w` is. -/
theorem isIso_map_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) {e : A ⟶ Z} (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    IsIso ((P.functor c₁).map ((P.functor c₂).map v)) ↔ IsIso ((P.functor w).map v) :=
  have := hiso
  (P.isIso_map_comp_iff c₁ c₂ v).symm.trans
    ((P.isIso_map_congr he v).trans (P.isIso_map_isIso_comp_iff e w v))

end Iterated

end ModulePullbackSystem

/-! ### The same three facts for the inverse image of Stacks 03LU itself -/

section ConcreteIterated

variable {A A' X Z : AlgebraicSpaces B S hS} {e : A ⟶ Z} {M N : Modules.{u, u} B S hS X.1 X.2}

/-- `AlgebraicGeometry.Space.ModulePullbackSystem.map_eq_zero_iterated_iff` for the inverse image
of Stacks 03LU itself, which is the system
`AlgebraicGeometry.Space.modulePullbackSystem`. -/
theorem modulePullback_map_eq_zero_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    (modulePullback B S hS c₁).map ((modulePullback B S hS c₂).map v) = 0 ↔
      (modulePullback B S hS w).map v = 0 :=
  (modulePullbackSystem B S hS).map_eq_zero_iterated_iff c₁ c₂ w hiso he v

/-- `AlgebraicGeometry.Space.ModulePullbackSystem.epi_map_iterated_iff` for the inverse image of
Stacks 03LU itself. -/
theorem modulePullback_epi_map_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    Epi ((modulePullback B S hS c₁).map ((modulePullback B S hS c₂).map v)) ↔
      Epi ((modulePullback B S hS w).map v) :=
  (modulePullbackSystem B S hS).epi_map_iterated_iff c₁ c₂ w hiso he v

/-- `AlgebraicGeometry.Space.ModulePullbackSystem.isIso_map_iterated_iff` for the inverse image
of Stacks 03LU itself. -/
theorem modulePullback_isIso_map_iterated_iff (c₁ : A ⟶ A') (c₂ : A' ⟶ X) (w : Z ⟶ X)
    (hiso : IsIso e) (he : c₁ ≫ c₂ = e ≫ w) (v : M ⟶ N) :
    IsIso ((modulePullback B S hS c₁).map ((modulePullback B S hS c₂).map v)) ↔
      IsIso ((modulePullback B S hS w).map v) :=
  (modulePullbackSystem B S hS).isIso_map_iterated_iff c₁ c₂ w hiso he v

end ConcreteIterated

namespace ModuleMapSituation

/-! ### The base-change space is a fibre product -/

variable (D : ModuleMapSituation.{u, u} B S hS)

/-- The base-change space of a test scheme is a fibre product: the projection to the source
space and the projection to the test scheme exhibit it as `X ×_Y T`. -/
theorem isPullback_baseChangeSpace (T : D.SchemesOver) :
    IsPullback (D.baseChangeProjection T) (D.baseChangeInclusion T) D.f T.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom

/-- The second projection of the base-change space commutes with a morphism of test schemes. -/
@[simp]
theorem baseChangeMap_comp_baseChangeInclusion {T T' : D.SchemesOver} (g : T' ⟶ T) :
    D.baseChangeMap g ≫ D.baseChangeInclusion T =
      D.baseChangeInclusion T' ≫ (schemeSpaceFunctor B S hS).map g.left :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift_snd _ _ _

/-! ### The base-changed standing datum -/

variable {Y' : AlgebraicSpaces B S hS} (b : Y' ⟶ D.Y)

/-- The source space of the base change along a morphism of the target space: `X ×_Y Y'`. -/
abbrev baseChangeTargetSpace : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS D.f b

/-- The projection `X ×_Y Y' ⟶ X`, along which the two modules and the map between them are
pulled back. -/
def baseChangeTargetProjection : D.baseChangeTargetSpace b ⟶ D.X :=
  ObjectProperty.homMk (pullback.fst D.f.hom b.hom)

/-- The structure morphism `X ×_Y Y' ⟶ Y'` of the base-changed situation. -/
def baseChangeTargetMorphism : D.baseChangeTargetSpace b ⟶ Y' :=
  ObjectProperty.homMk (pullback.snd D.f.hom b.hom)

/-- The source space of the base change is the fibre product `X ×_Y Y'`. -/
theorem isPullback_baseChangeTargetSpace :
    IsPullback (D.baseChangeTargetProjection b) (D.baseChangeTargetMorphism b) D.f b :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS D.f b

/-- The inverse image of the source module along the projection `X ×_Y Y' ⟶ X` is
quasi-coherent (Stacks 03GA). -/
theorem isQuasicoherentOnSite_baseChangeTargetF :
    ((modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.baseChangeTargetProjection b) D.F D.quasicoherent_F

/-- The inverse image of the target module along the projection `X ×_Y Y' ⟶ X` is
quasi-coherent (Stacks 03GA). -/
theorem isQuasicoherentOnSite_baseChangeTargetG :
    ((modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.baseChangeTargetProjection b) D.G D.quasicoherent_G

/-- The base change of the standing data of Stacks 083F along a morphism `b : Y' ⟶ Y` of the
target space: the source becomes `X ×_Y Y'`, the structure morphism the second projection, and
the two modules and the map between them their inverse images along the first projection
`X ×_Y Y' ⟶ X`. -/
@[reducible]
def baseChangeTarget : ModuleMapSituation.{u, u} B S hS where
  X := D.baseChangeTargetSpace b
  Y := Y'
  f := D.baseChangeTargetMorphism b
  F := (modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.F
  G := (modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.G
  quasicoherent_F := D.isQuasicoherentOnSite_baseChangeTargetF b
  quasicoherent_G := D.isQuasicoherentOnSite_baseChangeTargetG b
  u := (modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u

/-- The source space of the base-changed situation is `X ×_Y Y'`. -/
@[simp]
theorem baseChangeTarget_X : (D.baseChangeTarget b).X = D.baseChangeTargetSpace b :=
  rfl

/-- The target space of the base-changed situation is `Y'`. -/
@[simp]
theorem baseChangeTarget_Y : (D.baseChangeTarget b).Y = Y' :=
  rfl

/-- The structure morphism of the base-changed situation is the projection `X ×_Y Y' ⟶ Y'`. -/
@[simp]
theorem baseChangeTarget_f : (D.baseChangeTarget b).f = D.baseChangeTargetMorphism b :=
  rfl

/-- The source module of the base-changed situation is the inverse image of the source module
along `X ×_Y Y' ⟶ X`. -/
@[simp]
theorem baseChangeTarget_F :
    (D.baseChangeTarget b).F =
      (modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.F :=
  rfl

/-- The target module of the base-changed situation is the inverse image of the target module
along `X ×_Y Y' ⟶ X`. -/
@[simp]
theorem baseChangeTarget_G :
    (D.baseChangeTarget b).G =
      (modulePullback B S hS (D.baseChangeTargetProjection b)).obj D.G :=
  rfl

/-- The map of modules of the base-changed situation is the inverse image of `u` along
`X ×_Y Y' ⟶ X`. -/
@[simp]
theorem baseChangeTarget_u :
    (D.baseChangeTarget b).u =
      (modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u :=
  rfl

/-! ### The test schemes of the base change -/

/-- A test scheme over `Y'`, read as a test scheme over `Y` by composing its structure morphism
with `b`. -/
abbrev overTarget : (D.baseChangeTarget b).SchemesOver ⥤ D.SchemesOver :=
  CostructuredArrow.map b

/-- A test scheme over `Y'` read over `Y` has the same underlying scheme. -/
@[simp]
theorem overTarget_obj_left (T : (D.baseChangeTarget b).SchemesOver) :
    ((D.overTarget b).obj T).left = T.left :=
  rfl

/-- A test scheme over `Y'` read over `Y` has structure morphism its own followed by `b`. -/
@[simp]
theorem overTarget_obj_hom (T : (D.baseChangeTarget b).SchemesOver) :
    ((D.overTarget b).obj T).hom = T.hom ≫ b :=
  rfl

/-- A morphism of test schemes over `Y'` read over `Y` has the same underlying morphism of
schemes. -/
@[simp]
theorem overTarget_map_left {T T' : (D.baseChangeTarget b).SchemesOver} (g : T ⟶ T') :
    ((D.overTarget b).map g).left = g.left :=
  rfl

/-- The base change of the situation along the structure morphism of a test scheme `T` over
`Y`, viewed as an algebraic space over `Y` through `AlgebraicGeometry.schemeSpaceFunctor`. -/
abbrev baseChangeTestScheme (T : D.SchemesOver) : ModuleMapSituation.{u, u} B S hS :=
  D.baseChangeTarget T.hom

/-! ### The comparison of the two base-change spaces -/

/-- The comparison `(X ×_Y Y') ×_{Y'} T ≅ X ×_Y T` between the base change of `X ×_Y Y'` to a
test scheme `T` over `Y'` and the base change of `X` to `T` read as a test scheme over `Y`. -/
def baseChangeTargetSpaceIso (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).baseChangeSpace T ≅ D.baseChangeSpace ((D.overTarget b).obj T) :=
  ObjectProperty.isoMk _ (pullbackLeftPullbackSndIso D.f.hom b.hom T.hom.hom)

/-- The comparison of base-change spaces commutes with the projections to the source space, up
to the projection `X ×_Y Y' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem baseChangeTargetSpaceIso_hom_comp_baseChangeProjection
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTargetSpaceIso b T).hom ≫ D.baseChangeProjection ((D.overTarget b).obj T) =
      (D.baseChangeTarget b).baseChangeProjection T ≫ D.baseChangeTargetProjection b :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_fst D.f.hom b.hom T.hom.hom)

/-- The comparison of base-change spaces commutes with the projections to the test scheme. -/
@[reassoc (attr := simp)]
theorem baseChangeTargetSpaceIso_hom_comp_baseChangeInclusion
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTargetSpaceIso b T).hom ≫ D.baseChangeInclusion ((D.overTarget b).obj T) =
      (D.baseChangeTarget b).baseChangeInclusion T :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_snd D.f.hom b.hom T.hom.hom)

/-- The comparison of base-change spaces is natural in the test scheme. -/
theorem baseChangeTargetSpaceIso_naturality
    {T T' : (D.baseChangeTarget b).SchemesOver} (g : T' ⟶ T) :
    (D.baseChangeTarget b).baseChangeMap g ≫ (D.baseChangeTargetSpaceIso b T).hom =
      (D.baseChangeTargetSpaceIso b T').hom ≫ D.baseChangeMap ((D.overTarget b).map g) := by
  refine (D.isPullback_baseChangeSpace ((D.overTarget b).obj T)).hom_ext ?_ ?_
  · simp [reassoc_of% (baseChangeMap_comp_baseChangeProjection (D.baseChangeTarget b) g)]
  · simp

/-- The projection to `X` from the base change of `X ×_Y Y'` to a test scheme over `Y'`, as the
comparison of base-change spaces followed by the projection to `X` from the base change of `X`
to the same test scheme read over `Y`. -/
theorem baseChangeProjection_comp_baseChangeTargetProjection
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).baseChangeProjection T ≫ D.baseChangeTargetProjection b =
      (D.baseChangeTargetSpaceIso b T).hom ≫
        D.baseChangeProjection ((D.overTarget b).obj T) :=
  (D.baseChangeTargetSpaceIso_hom_comp_baseChangeProjection b T).symm

/-! ### The three conditions of Stacks 083F under base change of the target -/

/-- The base-changed map of the base-changed situation at a test scheme over `Y'`, written as an
iterated inverse image: first along `X ×_Y Y' ⟶ X`, then along the projection of the
base-change space. -/
theorem baseChangeHom_baseChangeTarget (P : ModulePullbackSystem.{u, u} B S hS)
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).baseChangeHom P T =
      (P.functor ((D.baseChangeTarget b).baseChangeProjection T)).map
        ((modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u) :=
  rfl

/-! #### The three comparisons at an arbitrary system -/

/-- The vanishing comparison at an arbitrary system whose functors are the inverse images of
Stacks 03LU. -/
private lemma isZeroAt_baseChangeTarget_iff_of (P : ModulePullbackSystem.{u, u} B S hS)
    (hP : ∀ {A A' : AlgebraicSpaces B S hS} (c : A ⟶ A'),
      P.functor c = modulePullback B S hS c)
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsZeroAt P T ↔ D.IsZeroAt P ((D.overTarget b).obj T) := by
  show (P.functor ((D.baseChangeTarget b).baseChangeProjection T)).map
        ((modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u) = 0 ↔
      (P.functor (D.baseChangeProjection ((D.overTarget b).obj T))).map D.u = 0
  rw [← hP (D.baseChangeTargetProjection b)]
  exact P.map_eq_zero_iterated_iff ((D.baseChangeTarget b).baseChangeProjection T)
    (D.baseChangeTargetProjection b) (D.baseChangeProjection ((D.overTarget b).obj T))
    (Iso.isIso_hom (D.baseChangeTargetSpaceIso b T))
    (D.baseChangeProjection_comp_baseChangeTargetProjection b T) D.u

/-- The surjectivity comparison at an arbitrary system whose functors are the inverse images of
Stacks 03LU. -/
private lemma isSurjectiveAt_baseChangeTarget_iff_of (P : ModulePullbackSystem.{u, u} B S hS)
    (hP : ∀ {A A' : AlgebraicSpaces B S hS} (c : A ⟶ A'),
      P.functor c = modulePullback B S hS c)
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsSurjectiveAt P T ↔
      D.IsSurjectiveAt P ((D.overTarget b).obj T) := by
  show Epi ((P.functor ((D.baseChangeTarget b).baseChangeProjection T)).map
        ((modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u)) ↔
      Epi ((P.functor (D.baseChangeProjection ((D.overTarget b).obj T))).map D.u)
  rw [← hP (D.baseChangeTargetProjection b)]
  exact P.epi_map_iterated_iff ((D.baseChangeTarget b).baseChangeProjection T)
    (D.baseChangeTargetProjection b) (D.baseChangeProjection ((D.overTarget b).obj T))
    (Iso.isIso_hom (D.baseChangeTargetSpaceIso b T))
    (D.baseChangeProjection_comp_baseChangeTargetProjection b T) D.u

/-- The isomorphism comparison at an arbitrary system whose functors are the inverse images of
Stacks 03LU. -/
private lemma isIsoAt_baseChangeTarget_iff_of (P : ModulePullbackSystem.{u, u} B S hS)
    (hP : ∀ {A A' : AlgebraicSpaces B S hS} (c : A ⟶ A'),
      P.functor c = modulePullback B S hS c)
    (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsIsoAt P T ↔ D.IsIsoAt P ((D.overTarget b).obj T) := by
  show IsIso ((P.functor ((D.baseChangeTarget b).baseChangeProjection T)).map
        ((modulePullback B S hS (D.baseChangeTargetProjection b)).map D.u)) ↔
      IsIso ((P.functor (D.baseChangeProjection ((D.overTarget b).obj T))).map D.u)
  rw [← hP (D.baseChangeTargetProjection b)]
  exact P.isIso_map_iterated_iff ((D.baseChangeTarget b).baseChangeProjection T)
    (D.baseChangeTargetProjection b) (D.baseChangeProjection ((D.overTarget b).obj T))
    (Iso.isIso_hom (D.baseChangeTargetSpaceIso b T))
    (D.baseChangeProjection_comp_baseChangeTargetProjection b T) D.u

/-- At a test scheme `T` over `Y'` the base-changed map of the base-changed situation is zero
exactly when the base-changed map of the original situation is zero at `T` read as a test
scheme over `Y`. -/
theorem isZeroAt_baseChangeTarget_iff (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsZeroAt (modulePullbackSystem B S hS) T ↔
      D.IsZeroAt (modulePullbackSystem B S hS) ((D.overTarget b).obj T) :=
  D.isZeroAt_baseChangeTarget_iff_of b (modulePullbackSystem B S hS)
    (fun c => modulePullbackSystem_functor B S hS c) T

/-- At a test scheme `T` over `Y'` the base-changed map of the base-changed situation is
surjective exactly when the base-changed map of the original situation is surjective at `T`
read as a test scheme over `Y`. -/
theorem isSurjectiveAt_baseChangeTarget_iff (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      D.IsSurjectiveAt (modulePullbackSystem B S hS) ((D.overTarget b).obj T) :=
  D.isSurjectiveAt_baseChangeTarget_iff_of b (modulePullbackSystem B S hS)
    (fun c => modulePullbackSystem_functor B S hS c) T

/-- At a test scheme `T` over `Y'` the base-changed map of the base-changed situation is an
isomorphism exactly when the base-changed map of the original situation is an isomorphism at
`T` read as a test scheme over `Y`. -/
theorem isIsoAt_baseChangeTarget_iff (T : (D.baseChangeTarget b).SchemesOver) :
    (D.baseChangeTarget b).IsIsoAt (modulePullbackSystem B S hS) T ↔
      D.IsIsoAt (modulePullbackSystem B S hS) ((D.overTarget b).obj T) :=
  D.isIsoAt_baseChangeTarget_iff_of b (modulePullbackSystem B S hS)
    (fun c => modulePullbackSystem_functor B S hS c) T

/-! ### The three subterminal functors under base change of the target -/

/-- The vanishing functor `F_zero` of Stacks 083F of the base-changed situation is that of the
original situation, restricted along `overTarget`. -/
def zeroFunctorBaseChangeTargetIso :
    (D.baseChangeTarget b).zeroFunctor (modulePullbackSystem B S hS) ≅
      (D.overTarget b).op ⋙ D.zeroFunctor (modulePullbackSystem B S hS) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      (Equiv.subtypeEquivRight fun _ => D.isZeroAt_baseChangeTarget_iff b T.unop))
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      rfl)

/-- The surjectivity functor of Stacks 083F of the base-changed situation is that of the
original situation, restricted along `overTarget`. -/
def surjFunctorBaseChangeTargetIso :
    (D.baseChangeTarget b).surjFunctor (modulePullbackSystem B S hS) ≅
      (D.overTarget b).op ⋙ D.surjFunctor (modulePullbackSystem B S hS) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      (Equiv.subtypeEquivRight fun _ => D.isSurjectiveAt_baseChangeTarget_iff b T.unop))
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      rfl)

/-- The isomorphism functor of Stacks 083F (Equation 77.7.1.1) of the base-changed situation is
that of the original situation, restricted along `overTarget`. -/
def isoFunctorBaseChangeTargetIso :
    (D.baseChangeTarget b).isoFunctor (modulePullbackSystem B S hS) ≅
      (D.overTarget b).op ⋙ D.isoFunctor (modulePullbackSystem B S hS) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      (Equiv.subtypeEquivRight fun _ => D.isIsoAt_baseChangeTarget_iff b T.unop))
    (fun _ => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      rfl)

/-! ### Identity and composition -/

/-- The square with the identity on both the source and the target space exhibits `X` itself as
the fibre product of `f` with the identity of `Y`. -/
theorem isPullback_id_target :
    IsPullback (𝟙 D.X) D.f D.f (𝟙 D.Y) :=
  IsPullback.of_horiz_isIso (fst := 𝟙 D.X) (snd := D.f) (f := D.f) (g := 𝟙 D.Y) ⟨by simp⟩

/-- Base changing along the identity of the target space does not change the source space, up
to the canonical comparison `X ×_Y Y ≅ X`. -/
def baseChangeTargetSpaceIdIso :
    D.baseChangeTargetSpace (𝟙 D.Y) ≅ D.X :=
  (D.isPullback_baseChangeTargetSpace (𝟙 D.Y)).isoIsPullback D.X D.Y D.isPullback_id_target

/-- The identity-law comparison is the projection to the source space. -/
@[simp]
theorem baseChangeTargetSpaceIdIso_hom :
    D.baseChangeTargetSpaceIdIso.hom = D.baseChangeTargetProjection (𝟙 D.Y) := by
  simpa [baseChangeTargetSpaceIdIso] using
    (D.isPullback_baseChangeTargetSpace (𝟙 D.Y)).isoIsPullback_hom_fst D.X D.Y
      D.isPullback_id_target

/-- Base changing along `b : Y' ⟶ Y` and then along `b' : Y'' ⟶ Y'` gives the same source space
as base changing along the composite, up to the canonical comparison
`(X ×_Y Y') ×_{Y'} Y'' ≅ X ×_Y Y''`. -/
def baseChangeTargetSpaceCompIso {Y'' : AlgebraicSpaces B S hS} (b' : Y'' ⟶ Y') :
    (D.baseChangeTarget b).baseChangeTargetSpace b' ≅ D.baseChangeTargetSpace (b' ≫ b) :=
  ObjectProperty.isoMk _ (pullbackLeftPullbackSndIso D.f.hom b.hom b'.hom)

/-- The composition-law comparison commutes with the projections to the source space. -/
@[reassoc (attr := simp)]
theorem baseChangeTargetSpaceCompIso_hom_comp_baseChangeTargetProjection
    {Y'' : AlgebraicSpaces B S hS} (b' : Y'' ⟶ Y') :
    (D.baseChangeTargetSpaceCompIso b b').hom ≫ D.baseChangeTargetProjection (b' ≫ b) =
      (D.baseChangeTarget b).baseChangeTargetProjection b' ≫ D.baseChangeTargetProjection b :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_fst D.f.hom b.hom b'.hom)

/-- The composition-law comparison commutes with the structure morphisms to the new target. -/
@[reassoc (attr := simp)]
theorem baseChangeTargetSpaceCompIso_hom_comp_baseChangeTargetMorphism
    {Y'' : AlgebraicSpaces B S hS} (b' : Y'' ⟶ Y') :
    (D.baseChangeTargetSpaceCompIso b b').hom ≫ D.baseChangeTargetMorphism (b' ≫ b) =
      (D.baseChangeTarget b).baseChangeTargetMorphism b' :=
  ObjectProperty.hom_ext _ (pullbackLeftPullbackSndIso_hom_snd D.f.hom b.hom b'.hom)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
