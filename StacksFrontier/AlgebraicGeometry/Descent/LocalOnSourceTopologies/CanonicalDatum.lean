module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData

/-!
# The canonical descent datum of a scheme over the base, and effective descent data

Let `f i : X i ⟶ S` be a family of morphisms of schemes with common target. Every scheme `U`
over `S` carries a canonical descent datum relative to that family: its component at `i` is the
fibre product `X i ×[S] U`, and its gluing isomorphisms are the ones that preserve the
projection to `U`. The assignment is functorial in `U`. A descent datum is *effective* when it
is isomorphic to the canonical descent datum of some scheme over `S`.

## Main definitions

* `AlgebraicGeometry.CanonicalDescentFunctor` bundles the canonical-datum functor with the
  identifications of its components, its action on morphisms, and the characterization of its
  gluing isomorphisms.
* `AlgebraicGeometry.canonicalFamilyDescentFunctor` is the canonical-datum functor itself.
* `AlgebraicGeometry.DescentData.IsFamilyEffective` is effectivity of a descent datum relative
  to a family.

## Implementation notes

The index type lives in a universe independent of the universe of schemes.

The components of the canonical datum are the pullbacks `(Over.pullback (f i)).obj U`, whose
underlying schemes are `U ×[S] X i`, with the factors in the opposite order to the source's
`X i ×_S U`. The gluing specification says that the transition map preserves the projection to
the original `S`-scheme; together with the compatibility over the pairwise base that every
descent datum carries, this characterizes the canonical transition map. The morphism
specification says the functor acts by componentwise base change, so its component
identifications are natural in `U`.

Bundling the functor with these three specifications lets a client use the component, morphism
and gluing API without unfolding the construction. Effectivity is an abbreviation for
membership in the essential image, so its existing API supplies both a scheme over `S` and an
isomorphism of descent data.

The names carry `Family` because the single-morphism case is already in the library under the
unqualified names: `AlgebraicGeometry.DescentData.canonicalFunctor` and
`AlgebraicGeometry.DescentData.IsEffective` are Tag 023Z, stated for a `Unit`-indexed descent
datum relative to one morphism `X ⟶ S`, and `AlgebraicGeometry.canonicalDescentFunctor` is
Tag 023D, the canonical descent datum of a quasi-coherent module. The declarations here are the
arbitrary-family generalization of the first pair.

## References

* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- A functorial choice of the canonical descent datum of an `S`-scheme for a family
`f i : X i ⟶ S`. Its gluing maps preserve the projection to the original `S`-scheme. -/
structure CanonicalDescentFunctor {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) where
  /-- The functor assigning the canonical descent datum. -/
  functor : Over S ⥤ DescentData f
  /-- Its component at `i` is the pullback of the scheme over `S`. -/
  obj (U : Over S) (i : I) :
    (functor.obj U).obj i = (Over.pullback (f i)).obj U
  /-- On morphisms the functor is componentwise pullback. -/
  map {U V : Over S} (g : U ⟶ V) (i : I) :
    (functor.map g).hom i ≫ eqToHom (obj V i) =
      eqToHom (obj U i) ≫ (Over.pullback (f i)).map g
  /-- The canonical gluing preserves the projection to `U`. -/
  gluing (U : Over S) (i j : I) :
    ((functor.obj U).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (((functor.obj U).obj j).hom ≫ f j) ≫
        (eqToHom (obj U j)).left ≫ pullback.fst U.hom (f j) =
      pullback.fst (((functor.obj U).obj i).hom ≫ f i) (f j) ≫
        (eqToHom (obj U i)).left ≫ pullback.fst U.hom (f i)

namespace CanonicalDatum

/-- The component `(Over.map f).obj ((Over.pullback f).obj U)` of the canonical datum, viewed
as a scheme over `S`. -/
abbrev component {S X : Scheme.{u}} (U : Over S) (f : X ⟶ S) :=
  (Over.map f).obj ((Over.pullback f).obj U)

/-- The projection of a component of the canonical datum to the original `S`-scheme. -/
def originalProjection {S X : Scheme.{u}} (U : Over S) (f : X ⟶ S) :
    component U f ⟶ U :=
  Over.homMk (pullback.fst U.hom f) pullback.condition

/-- A map into a component of the canonical datum, given its two projections. -/
def componentLift {S X : Scheme.{u}} {U T : Over S} {f : X ⟶ S}
    (a : T ⟶ U) (b : T ⟶ Over.mk f) : T ⟶ component U f :=
  Over.homMk (pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd U.hom f ≫ f = T.hom
      rw [pullback.lift_snd_assoc]
      exact Over.w b)

/-- The lift into a component, followed by the projection to the original `S`-scheme, is the
first given map. -/
@[reassoc (attr := simp)]
lemma componentLift_original {S X : Scheme.{u}} {U T : Over S} {f : X ⟶ S}
    (a : T ⟶ U) (b : T ⟶ Over.mk f) :
    componentLift a b ≫ originalProjection U f = a :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The lift into a component, followed by its structure map to `X`, is the second given map. -/
@[reassoc (attr := simp)]
lemma componentLift_structure {S X : Scheme.{u}} {U T : Over S} {f : X ⟶ S}
    (a : T ⟶ U) (b : T ⟶ Over.mk f) :
    componentLift a b ≫ structureMap f ((Over.pullback f).obj U) = b :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- Two maps into a component of the canonical datum are equal if they agree after the
projection to the original `S`-scheme and after the structure map to `X`. -/
lemma component_hom_ext {S X : Scheme.{u}} {U T : Over S} {f : X ⟶ S}
    {a b : T ⟶ component U f}
    (h₁ : a ≫ originalProjection U f = b ≫ originalProjection U f)
    (h₂ : a ≫ structureMap f ((Over.pullback f).obj U) =
      b ≫ structureMap f ((Over.pullback f).obj U)) : a = b :=
  Over.OverMorphism.ext
    (pullback.hom_ext (congrArg Over.Hom.left h₁) (congrArg Over.Hom.left h₂))

/-- Base change of a morphism `g : U ⟶ V` commutes with the projections of the components to
the original `S`-schemes. -/
@[reassoc (attr := simp)]
lemma componentMap_original {S X : Scheme.{u}} {U V : Over S}
    (g : U ⟶ V) (f : X ⟶ S) :
    (Over.map f).map ((Over.pullback f).map g) ≫ originalProjection V f =
      originalProjection U f ≫ g :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- Base change of a morphism `g : U ⟶ V` commutes with the structure maps of the components
to `X`. -/
@[reassoc (attr := simp)]
lemma componentMap_structure {S X : Scheme.{u}} {U V : Over S}
    (g : U ⟶ V) (f : X ⟶ S) :
    (Over.map f).map ((Over.pullback f).map g) ≫
        structureMap f ((Over.pullback f).obj V) =
      structureMap f ((Over.pullback f).obj U) :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- The transition map of the canonical descent datum over the pairwise base. -/
def transition {S X Y : Scheme.{u}} (U : Over S) (f : X ⟶ S) (g : Y ⟶ S) :
    component U f ⨯ Over.mk g ⟶ Over.mk f ⨯ component U g :=
  prod.lift (prod.fst ≫ structureMap f ((Over.pullback f).obj U))
    (componentLift (prod.fst ≫ originalProjection U f) prod.snd)

/-- The first factor of the transition map is the structure map of the component to `X`. -/
@[reassoc (attr := simp)]
lemma transition_fst {S X Y : Scheme.{u}} (U : Over S)
    (f : X ⟶ S) (g : Y ⟶ S) :
    transition U f g ≫ prod.fst = prod.fst ≫ structureMap f ((Over.pullback f).obj U) := by
  simp [transition]

/-- The transition map preserves the projection to the original `S`-scheme. -/
@[reassoc (attr := simp)]
lemma transition_original {S X Y : Scheme.{u}} (U : Over S)
    (f : X ⟶ S) (g : Y ⟶ S) :
    transition U f g ≫ prod.snd ≫ originalProjection U g =
      prod.fst ≫ originalProjection U f := by
  simp [transition]

/-- The transition map, followed by the structure map of the second component to `Y`, is the
second projection. -/
@[reassoc (attr := simp)]
lemma transition_structure {S X Y : Scheme.{u}} (U : Over S)
    (f : X ⟶ S) (g : Y ⟶ S) :
    transition U f g ≫ prod.snd ≫ structureMap g ((Over.pullback g).obj U) =
      prod.snd := by
  simp [transition]

/-- The transition map of the canonical descent datum is an isomorphism. -/
def transitionIso {S X Y : Scheme.{u}} (U : Over S)
    (f : X ⟶ S) (g : Y ⟶ S) :
    component U f ⨯ Over.mk g ≅ Over.mk f ⨯ component U g where
  hom := transition U f g
  inv := prod.lift (componentLift (prod.snd ≫ originalProjection U g) prod.fst)
    (prod.snd ≫ structureMap g ((Over.pullback g).obj U))
  hom_inv_id := by
    apply prod.hom_ext
    · apply component_hom_ext <;> simp
    · simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply component_hom_ext <;> simp

/-- The canonical descent datum of a scheme over the base. -/
def datum {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) (U : Over S) : DescentData f where
  obj i := (Over.pullback (f i)).obj U
  gluing i j := Over.isoMk (transitionIso U (f i) (f j)) (by
    apply prod.hom_ext <;> simp [transitionIso])
  cocycle i j k := by
    change prod.map (transition U (f i) (f j)) (𝟙 _) ≫
      prodMapLastTwo (transition U (f j) (f k)) =
        prodMapFirstThird (transition U (f i) (f k))
    apply prod.hom_ext
    · apply prod.hom_ext <;> simp [prodMapLastTwo, prodMapFirstThird]
    · apply component_hom_ext <;> simp [prodMapLastTwo, prodMapFirstThird]

/-- The canonical descent datum is functorial in the scheme over the base. -/
def functor {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) : Over S ⥤ DescentData f where
  obj := datum f
  map {U V} g :=
    { hom i := (Over.pullback (f i)).map g
      comm i j := by
        change prod.map ((Over.map (f i)).map ((Over.pullback (f i)).map g)) (𝟙 _) ≫
          transition V (f i) (f j) = transition U (f i) (f j) ≫
            prod.map (𝟙 _) ((Over.map (f j)).map ((Over.pullback (f j)).map g))
        apply prod.hom_ext
        · simp
        · apply component_hom_ext <;> simp }
  map_id U := DescentData.hom_ext fun i ↦ (Over.pullback (f i)).map_id U
  map_comp g h := DescentData.hom_ext fun i ↦ (Over.pullback (f i)).map_comp g h

/-- The gluing isomorphism of the canonical descent datum preserves the projection to the
original scheme over `S`. -/
public lemma datum_gluing_proj {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (U : Over S) (i j : I) :
    ((datum f U).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (pullback.snd U.hom (f j) ≫ f j) ≫
        pullback.fst U.hom (f j) =
      pullback.fst (pullback.snd U.hom (f i) ≫ f i) (f j) ≫
        pullback.fst U.hom (f i) := by
  simp only [DescentData.gluingPullbackIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
  dsimp only [datum]
  show _ ≫ _ ≫ (Over.prodLeftIsoPullback (Over.mk (f i)) (component U (f j))).hom ≫
    pullback.snd (Over.mk (f i)).hom (component U (f j)).hom ≫ _ = _
  rw [Over.prodLeftIsoPullback_hom_snd_assoc]
  have h := congrArg Over.Hom.left (transition_original U (f i) (f j))
  simp only [Over.comp_left] at h
  show _ ≫ (transition U (f i) (f j)).left ≫
    (prod.snd : Over.mk (f i) ⨯ component U (f j) ⟶ _).left ≫
    (originalProjection U (f j)).left = _
  rw [h]
  exact Over.prodLeftIsoPullback_inv_fst_assoc _ _ _

end CanonicalDatum

open CanonicalDatum in
/-- The canonical descent datum functor for an arbitrarily indexed family of schemes over `S`:
it sends a scheme `U` over `S` to the descent datum whose components are the fibre products of
`U` with the members of the family, with the gluing isomorphisms that preserve the projection to
`U`. -/
@[stacks 02VU "part (1)", implicit_reducible]
def canonicalFamilyDescentFunctor {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    CanonicalDescentFunctor f where
  functor := CanonicalDatum.functor f
  obj _ _ := rfl
  map g i := by
    change (Over.pullback _).map _ ≫ 𝟙 _ = 𝟙 _ ≫ (Over.pullback _).map _
    simp only [Category.comp_id, Category.id_comp]
  gluing U i j := by
    change ((datum f U).gluingPullbackIso i j).hom ≫
        pullback.snd (f i) (pullback.snd U.hom (f j) ≫ f j) ≫
        (𝟙 _) ≫ pullback.fst U.hom (f j) =
      pullback.fst (pullback.snd U.hom (f i) ≫ f i) (f j) ≫
        (𝟙 _) ≫ pullback.fst U.hom (f i)
    simp only [Category.id_comp, DescentData.gluingPullbackIso, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
    dsimp only [datum]
    change _ ≫ _ ≫ (Over.prodLeftIsoPullback (Over.mk (f i)) (component U (f j))).hom ≫
      pullback.snd (Over.mk (f i)).hom (component U (f j)).hom ≫ _ = _
    rw [Over.prodLeftIsoPullback_hom_snd_assoc]
    have h := congrArg Over.Hom.left (transition_original U (f i) (f j))
    simp only [Over.comp_left] at h
    change _ ≫ (transition U (f i) (f j)).left ≫
      (prod.snd : Over.mk (f i) ⨯ component U (f j) ⟶ _).left ≫
      (originalProjection U (f j)).left = _
    rw [h]
    exact Over.prodLeftIsoPullback_inv_fst_assoc _ _ _


namespace DescentData

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- A descent datum relative to a family is effective if it is isomorphic to the canonical
descent datum of some scheme over the common base. -/
@[stacks 02VU "part (2)", sga "3 IV 3.5.1"]
abbrev IsFamilyEffective (D : DescentData f) : Prop :=
  (canonicalFamilyDescentFunctor f).functor.essImage D

end DescentData

end AlgebraicGeometry

end

end
