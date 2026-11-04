module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# Compatible systems of sheaves on the small étale sites

Let `B` be a big étale site containing a scheme `S`. A sheaf on the big étale site over `S`
restricts, for every scheme `T` over `S`, to a sheaf on the small étale site of `T`, and these
restrictions are related by comparison maps along every morphism over `S`. This file isolates
the resulting structure: a sheaf on the small étale site of each `T`, a map from the inverse
image of the sheaf at `T` to the sheaf at `T'` for every `f : T' ⟶ T`, compatible with
composition and an isomorphism whenever `f` is étale.

## Main definitions

* `AlgebraicGeometry.BigEtaleSheafData` — the compatible data: a sheaf on each small étale
  site, the comparison maps, the cocycle condition and the étale isomorphism condition.
* `AlgebraicGeometry.BigEtaleSheafData.Hom` and the category structure it carries, with
  `AlgebraicGeometry.BigEtaleSheafData.eval` the evaluation at one scheme over `S`.
* `AlgebraicGeometry.bigEtaleSheafRestrictionAt` — restriction of a big étale sheaf to the small
  étale site of a scheme over `S`.
* `AlgebraicGeometry.bigEtaleBaseChangeProjection` — the projection `U ×[T] T' ⟶ U`, read as a
  morphism of the big étale site over `S`.

## Implementation notes

The comparison maps are written on inverse images, as in the source. The cocycle condition uses
the canonical composition isomorphism of inverse images of small étale sheaves, which is
necessary because the fibre products defining base change are chosen, so successive base
changes agree with base change along a composite only up to canonical isomorphism.

The independent universe `v` lets the sheaves take values in `Type (max (u + 1) v)`. The lower
bound `u + 1` is what the colimits and the sheafification over these sites require; it is no
restriction on the schemes or the sheaves.

## References

* [Stacks Project, Tag 021K](https://stacks.math.columbia.edu/tag/021K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A compatible system of sheaves on the small étale sites of the schemes over `S`: a sheaf on
the small étale site of every `T / S`, a comparison map from the inverse image of the sheaf at `T`
to the sheaf at `T'` along every morphism `T' ⟶ T` over `S`, subject to the cocycle condition for
a composite and to being an isomorphism whenever the morphism is étale. -/
@[stacks 021K "the compatible data"]
public structure BigEtaleSheafData where
  /-- The small étale sheaf on each scheme over `S`. -/
  sheaf (T : BigEtaleOver B S hS) :
    Sheaf (SmallEtale.topology B T.left.1 T.left.property) (Type (max (u + 1) v))
  /-- Pullback comparison along a morphism over `S`. -/
  pullback {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (B.smallInverseImage f.left (Type (max (u + 1) v))).obj (sheaf T) ⟶ sheaf T'
  /-- The pullback comparisons are compatible with composition. -/
  pullback_comp {T T' T'' : BigEtaleOver B S hS}
      (f : T' ⟶ T) (g : T'' ⟶ T') :
    (B.smallInverseImage g.left (Type (max (u + 1) v))).map (pullback f) ≫ pullback g =
      (smallEtaleSheafPullbackCompIso B T''.left T'.left T.left g.left f.left
        (Type (max (u + 1) v))).hom.app (sheaf T) ≫ pullback (g ≫ f)
  /-- Étale morphisms give isomorphisms on small étale sheaves. -/
  isIso_pullback {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
      [Etale (B.inclusion.map f.left)] : IsIso (pullback f)

/-- A morphism of compatible systems: a morphism of sheaves on every small étale site,
commuting with all the comparison maps. -/
public structure BigEtaleSheafData.Hom (D E : BigEtaleSheafData.{u, v} B S hS) where
  /-- The morphism on each small étale site. -/
  app (T : BigEtaleOver B S hS) : D.sheaf T ⟶ E.sheaf T
  /-- Compatibility with pullback along every morphism over the base. -/
  naturality {T T' : BigEtaleOver B S hS} (f : T' ⟶ T) :
    (B.smallInverseImage f.left (Type (max (u + 1) v))).map (app T) ≫ E.pullback f =
      D.pullback f ≫ app T'

/-- A morphism of compatible systems is determined by its components. -/
@[ext] public theorem BigEtaleSheafData.Hom.ext
    {D E : BigEtaleSheafData.{u, v} B S hS}
    {φ ψ : BigEtaleSheafData.Hom B S hS D E}
    (h : ∀ T, φ.app T = ψ.app T) : φ = ψ := by
  cases φ
  cases ψ
  congr 1
  exact funext h

/-- Compatible systems of small étale sheaves over `S` form a category, with composition taken
componentwise. -/
public instance : Category (BigEtaleSheafData.{u, v} B S hS) where
  Hom := BigEtaleSheafData.Hom B S hS
  id D := ⟨fun T => 𝟙 _, by intro T T' f; simp⟩
  comp φ ψ := ⟨fun T => φ.app T ≫ ψ.app T, by
    intro T T' f
    simp only [Functor.map_comp]
    rw [Category.assoc, ψ.naturality f, ← Category.assoc, φ.naturality f,
      Category.assoc]⟩
  id_comp _ := BigEtaleSheafData.Hom.ext _ _ _ fun _ => by simp
  comp_id _ := BigEtaleSheafData.Hom.ext _ _ _ fun _ => by simp
  assoc _ _ _ := BigEtaleSheafData.Hom.ext _ _ _ fun _ => by simp only [Category.assoc]

/-- Evaluation of a compatible system on the small étale site of one scheme over `S`. -/
public def BigEtaleSheafData.eval (T : BigEtaleOver B S hS) :
    BigEtaleSheafData.{u, v} B S hS ⥤
      Sheaf (SmallEtale.topology B T.left.1 T.left.property) (Type (max (u + 1) v)) where
  obj D := D.sheaf T
  map φ := φ.app T

/-- Restriction of a sheaf on the big étale site over `S` to the small étale site of a scheme
`T` over `S`, on both sheaves and morphisms. It is the inverse image along the morphism of
topoi from the small étale topos of `T` to the big étale topos over `S`. -/
public def bigEtaleSheafRestrictionAt (T : BigEtaleOver B S hS) :
    Sheaf (BigEtaleOver.topology B S hS) (Type (max (u + 1) v)) ⥤
      Sheaf (SmallEtale.topology B T.left.1 T.left.property) (Type (max (u + 1) v)) := by
  haveI := smallEtaleToBigEtaleFunctor_isContinuous B T.left (B.obj S hS) T.hom
  exact Functor.sheafPushforwardContinuous
    (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom)
    (Type (max (u + 1) v))
    (SmallEtale.topology B T.left.1 T.left.property) (BigEtaleOver.topology B S hS)

/-- The projection `U ×[T] T' ⟶ U` of an étale scheme `U` over `T` along a morphism `T' ⟶ T`
over `S`, regarded as a morphism of the big étale site over `S`. -/
public def bigEtaleBaseChangeProjection {T T' : BigEtaleOver B S hS} (f : T' ⟶ T)
    (U : SmallEtale B T.left.1 T.left.property) :
    (smallEtaleToBigEtaleFunctor B T'.left (B.obj S hS) T'.hom).obj
        ((smallEtaleBaseChange B f.left).obj U) ⟶
      (smallEtaleToBigEtaleFunctor B T.left (B.obj S hS) T.hom).obj U :=
  Over.homMk (pullback.fst U.obj.hom f.left) (by
    change pullback.fst U.obj.hom f.left ≫ (U.obj.hom ≫ T.hom) =
      pullback.snd U.obj.hom f.left ≫ T'.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, Over.w f])

end AlgebraicGeometry

end
