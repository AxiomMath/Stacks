module

public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageComposition

/-!
# The morphism of inverse-image ringed spaces attached to a commutative square

For a commutative square of schemes `g' ≫ f = f' ≫ g` this file constructs the morphism of
ringed spaces `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` with underlying map that of `g'`, and
proves that it lies over `g` and under `g'`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

namespace Stacks.DeRhamBaseChange

section RingChange

variable {X' S' S : Scheme.{u}} (f' : X' ⟶ S') (g : S' ⟶ S)

/-- The transpose of the structure map of `baseRingChange`: `g^♯` followed by the direct image
along `g` of the unit of `f'^{-1} ⊣ f'_*` at `𝒪_{S'}`. -/
def baseRingChangeAdj : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f' ≫ g).base).obj
    ((TopCat.Sheaf.pullback CommRingCat.{u} f'.base).obj S'.sheaf) :=
  (⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj S'.sheaf) ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f'.base).unit.app S'.sheaf)

/-- **The change of the base ring** `(X', f'^{-1}𝒪_{S'}) ⟶ (X', (f' ∘ g)^{-1}𝒪_S)`: the identity
on spaces, with structure map `(f' ∘ g)^{-1}𝒪_S ⟶ f'^{-1}𝒪_{S'}` the transpose of `g^♯`. -/
def baseRingChange : inverseImageBase f' ⟶ inverseImageBase (f' ≫ g) :=
  InducedCategory.homMk
    { base := 𝟙 X'.carrier
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f' ≫ g).base).homEquiv
        _ _).symm (baseRingChangeAdj f' g)).hom }

/-- Morphisms of ringed spaces with equal underlying maps are equal once their structure maps
agree. -/
private theorem ringedSpace_hom_ext_of_c_eq {A B : RingedSpace.{u}} {φ ψ : A ⟶ B}
    (hb : φ.hom.base = ψ.hom.base) (hc : φ.hom.c ≍ ψ.hom.c) : φ = ψ :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ hb hc)

/-- The change of the base ring lies over `g`. -/
theorem baseRingChange_comp_inverseImageBaseProjection :
    baseRingChange f' g ≫ inverseImageBaseProjection (f' ≫ g) =
      inverseImageBaseProjection f' ≫ g.toLRSHom.toShHom := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f' ≫ g).base).homEquiv
    S.sheaf _ |>.apply_symm_apply (baseRingChangeAdj f' g)
  exact ringedSpace_hom_ext_of_c_eq rfl (heq_of_eq (congrArg (fun t => t.hom) h))

/-- The change of the base ring is compatible with the structural maps to `𝒪_{X'}`. -/
theorem toInverseImageBase_comp_baseRingChange :
    toInverseImageBase f' ≫ baseRingChange f' g = toInverseImageBase (f' ≫ g) := by
  have key : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f' ≫ g).base).homEquiv
      _ _).symm (baseRingChangeAdj f' g) ≫ inverseImageStructureMap f' =
        inverseImageStructureMap (f' ≫ g) := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f' ≫ g).base).homEquiv
      _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    refine Eq.trans ?_ (Equiv.apply_symm_apply ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} (f' ≫ g).base).homEquiv S.sheaf X'.sheaf)
        (⟨(f' ≫ g).c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f' ≫ g).base).obj
          X'.sheaf)).symm
    have h1 := Scheme.Hom.unit_comp_pushforward_inverseImageStructureMap f'
    exact (Category.assoc _ _ _).trans (congrArg (fun t => (⟨g.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj S'.sheaf) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map t) h1)
  exact ringedSpace_hom_ext_of_c_eq rfl (heq_of_eq (congrArg (fun t => t.hom) key))

end RingChange

section Square

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

/-- The canonical morphism `(X', h^{-1}𝒪_S) ⟶ (X, f^{-1}𝒪_S)` over `g'`, for a morphism `h`
presented as the composite `g' ≫ f`. Its underlying continuous map is literally that of `g'`;
only the structure map is transported along `g' ≫ f = h`. -/
def relativeBaseOfEq {h : X' ⟶ S} (hh : g' ≫ f = h) : inverseImageBase h ⟶ inverseImageBase f :=
  InducedCategory.homMk
    { base := g'.base
      c := (relativeBase g' f).hom.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} g'.base).map
        (eqToHom (congrArg (fun k : X' ⟶ S =>
          ((TopCat.Sheaf.pullback CommRingCat.{u} k.base).obj S.sheaf).obj) hh)) }

/-- At the literal composite the transported morphism is `relativeBase`. -/
theorem relativeBaseOfEq_rfl : relativeBaseOfEq g' f rfl = relativeBase g' f := by
  refine ringedSpace_hom_ext_of_c_eq rfl (heq_of_eq ?_)
  exact (congrArg (fun t => (relativeBase g' f).hom.c ≫
    (TopCat.Presheaf.pushforward CommRingCat.{u} g'.base).map t) (eqToHom_refl _ rfl)).trans
      ((congrArg ((relativeBase g' f).hom.c ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
        (Category.comp_id _))

/-- The canonical morphism over `g'` lies over `S`. -/
theorem relativeBaseOfEq_comp_inverseImageBaseProjection {h : X' ⟶ S} (hh : g' ≫ f = h) :
    relativeBaseOfEq g' f hh ≫ inverseImageBaseProjection f = inverseImageBaseProjection h := by
  subst hh
  rw [relativeBaseOfEq_rfl]
  exact RingedSpace.inverseImageCompProjection_comp S.toRingedSpace f.base g'.base

/-- The canonical morphism over `g'` is compatible with the structural maps. -/
theorem toInverseImageBase_comp_relativeBaseOfEq {h : X' ⟶ S} (hh : g' ≫ f = h) :
    toInverseImageBase h ≫ relativeBaseOfEq g' f hh =
      g'.toLRSHom.toShHom ≫ toInverseImageBase f := by
  subst hh
  rw [relativeBaseOfEq_rfl]
  exact Stacks.DeRhamPullback.toInverseImageBase_relativeBase g' f

/-- **The morphism of inverse-image ringed spaces attached to a commutative square**
`(X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)`, with underlying continuous map that of `g'`: the change
of base ring along `g`, followed by the canonical morphism over `g'`. -/
def inverseImageBaseMap (w : g' ≫ f = f' ≫ g) : inverseImageBase f' ⟶ inverseImageBase f :=
  baseRingChange f' g ≫ relativeBaseOfEq g' f w

/-- The morphism of inverse-image ringed spaces lies over `g`: the square

```
(X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)
        |                    |
        S'        ⟶          S
```

of ringed spaces commutes. -/
theorem inverseImageBaseMap_comp_inverseImageBaseProjection (w : g' ≫ f = f' ≫ g) :
    inverseImageBaseMap g' f' f g w ≫ inverseImageBaseProjection f =
      inverseImageBaseProjection f' ≫ g.toLRSHom.toShHom := by
  rw [inverseImageBaseMap, Category.assoc, relativeBaseOfEq_comp_inverseImageBaseProjection,
    baseRingChange_comp_inverseImageBaseProjection]

/-- The morphism of inverse-image ringed spaces lies under `g'`: the square

```
(X', 𝒪_{X'})        ⟶ (X, 𝒪_X)
      |                    |
(X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)
```

of ringed spaces commutes. -/
theorem toInverseImageBase_comp_inverseImageBaseMap (w : g' ≫ f = f' ≫ g) :
    toInverseImageBase f' ≫ inverseImageBaseMap g' f' f g w =
      g'.toLRSHom.toShHom ≫ toInverseImageBase f := by
  rw [inverseImageBaseMap, ← Category.assoc, toInverseImageBase_comp_baseRingChange,
    toInverseImageBase_comp_relativeBaseOfEq]

end Square

end Stacks.DeRhamBaseChange
