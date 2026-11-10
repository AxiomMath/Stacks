module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# Flatness over an étale intermediate scheme

Let `X ⟶ T ⟶ S` be morphisms of schemes, with `T ⟶ S` étale. A quasi-coherent module on `X`
is flat over `S` at a point precisely when it is flat over `T` there. Consequently, flatness
over either base is equivalent.

The forward implication is the substantial one: the graph of `X ⟶ T` is an open immersion into
`X ×_S T`, because the diagonal of an étale — hence unramified — morphism is, so flatness over
`S` of the module transfers to its pullback along the first projection by base change, and the
graph identifies that pullback over `T` with the module itself. The converse is the composition
property of flatness over a base, applied to the flat morphism `T ⟶ S`.

## Main results

* `AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale` compares flatness at a point over the two
  bases.
* `AlgebraicGeometry.isFlatOver_comp_iff_of_etale` compares global flatness over the two bases.

## Implementation notes

The source's pointwise assertion and its global consequence are stated separately. Flatness of
a module over a base is the stalkwise predicate `AlgebraicGeometry.IsFlatOverAt`, applied to the
underlying morphisms of ringed spaces of the schemes.

## References

* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

section Helpers

open CategoryTheory.Limits RingedSpaceModuleAdjunction

/-- The graph of a morphism `X ⟶ T` over an unramified morphism `T ⟶ S` is an open immersion
into the fibre product of `X ⟶ S` with `T ⟶ S`. -/
private lemma isOpenImmersion_graph {X T S : Scheme.{u}} (f : X ⟶ T)
    (g : T ⟶ S) [AlgebraicGeometry.Unramified g] :
    IsOpenImmersion (pullback.lift (𝟙 X) f (by simp : 𝟙 X ≫ f ≫ g = f ≫ g)) := by
  have : IsOpenImmersion (pullback.mapDesc f (𝟙 T) g) :=
    MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f (𝟙 T) g)
      (AlgebraicGeometry.Unramified.isOpenImmersion_diagonal g)
  let i : X ⟶ pullback (f ≫ g) g :=
    pullback.lift (𝟙 X) f (by simp : 𝟙 X ≫ f ≫ g = f ≫ g)
  let e := pullback.congrHom (f₁ := f ≫ g) (f₂ := f ≫ g)
    (g₁ := g) (g₂ := 𝟙 T ≫ g) rfl (Category.id_comp g)
  have hi : pullback.fst f (𝟙 T) ≫ i ≫ e.hom =
      pullback.mapDesc f (𝟙 T) g := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, i, e, pullback.mapDesc, pullback.congrHom, pullback.map]
    · erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
      simp [pullback.condition (f := f) (g := 𝟙 T)]
  have hc : IsOpenImmersion (pullback.fst f (𝟙 T) ≫ i ≫ e.hom) := by
    rw [hi]
    infer_instance
  exact (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion i e.hom).mp
    ((MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (pullback.fst f (𝟙 T)) (i ≫ e.hom)).mp hc)

end Helpers

variable {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
  (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
  [F.IsQuasicoherent]

section Pointwise

open CategoryTheory.Limits RingedSpaceModuleAdjunction

/-- Flatness of a quasi-coherent module at a point is unchanged when the base
is replaced by an étale intermediate scheme. -/
@[stacks 05B9 "pointwise statement"]
public theorem isFlatOverAt_comp_iff_of_etale [Etale g] (x : X) :
    AlgebraicGeometry.IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x ↔
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x := by
  constructor
  · intro hF
    have : AlgebraicGeometry.Unramified g := ⟨fun y =>
      ((etaleAt_iff_smoothAt_and_unramifiedAt g y).mp ((etale_iff_forall_etaleAt g).mp ‹_› y)).2⟩
    let P := pullback (f ≫ g) g
    let p₁ : P ⟶ X := pullback.fst (f ≫ g) g
    let p₂ : P ⟶ T := pullback.snd (f ≫ g) g
    let i : X ⟶ P := pullback.lift (𝟙 X) f (by simp : 𝟙 X ≫ (f ≫ g) = f ≫ g)
    let Fm : SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace) := F
    have : Fm.IsQuasicoherent := ‹F.IsQuasicoherent›
    have hi₁ : i ≫ p₁ = 𝟙 X := pullback.lift_fst _ _ _
    have hi₂ : i ≫ p₂ = f := pullback.lift_snd _ _ _
    have : IsOpenImmersion i := isOpenImmersion_graph f g
    let F' := (modulePullback p₁.toLRSHom.toShHom).obj Fm
    have hpoint : p₁ (i x) = x := congrArg (fun k : X ⟶ X => k x) hi₁
    have hF' : IsFlatOverAt (f ≫ g).toLRSHom.toShHom Fm (p₁ (i x)) := by rw [hpoint]; exact hF
    have hback := modulePullback_isFlatOverAt
      (IsPullback.of_hasPullback (f ≫ g) g) Fm (i x) hF'
    have hiFlat : AlgebraicGeometry.IsFlatAt i.toLRSHom.toShHom x := by
      change (i.stalkMap x).hom.Flat
      exact Flat.stalkMap i x
    have hres := (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
      i p₂ F' x hiFlat).mp hback
    have hid : i.toLRSHom.toShHom ≫ p₁.toLRSHom.toShHom = 𝟙 _ := by
      rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom, hi₁]
      change LocallyRingedSpace.Hom.toShHom
        (𝟙 X.toLocallyRingedSpace) = 𝟙 (X.toSheafedSpace)
      exact LocallyRingedSpace.id_toShHom' X.toLocallyRingedSpace
    let epull : (modulePullback i.toLRSHom.toShHom).obj F' ≅ Fm :=
      ((Stacks.PullbackPseudofunctor.modulePullbackCompIso
          p₁.toLRSHom.toShHom i.toLRSHom.toShHom).app Fm).symm ≪≫
        (eqToIso (congrArg modulePullback hid)).app Fm ≪≫
        (Stacks.PullbackPseudofunctor.modulePullbackIdIso _).app Fm
    have hsame :=
      (isFlatOverAt_iff_of_moduleIso (i ≫ p₂).toLRSHom.toShHom epull x).mp hres
    rwa [hi₂] at hsame
  · intro hF
    apply IsFlatOverAt.comp f.toLRSHom.toShHom g.toLRSHom.toShHom F x hF
    change (g.stalkMap (f x)).hom.Flat
    exact Flat.stalkMap g (f x)

/-- A quasi-coherent module is flat over the base if and only if it is flat
over an étale intermediate scheme. -/
@[stacks 05B9 "global statement"]
public theorem isFlatOver_comp_iff_of_etale [Etale g] :
    AlgebraicGeometry.IsFlatOver (f ≫ g).toLRSHom.toShHom F ↔
      AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F := by
  change (∀ x : X, AlgebraicGeometry.IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x) ↔
    ∀ x : X, AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x
  exact forall_congr' fun x => isFlatOverAt_comp_iff_of_etale f g F x

end Pointwise

end AlgebraicGeometry
