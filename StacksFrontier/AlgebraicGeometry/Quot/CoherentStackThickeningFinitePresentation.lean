module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FlatIdealTensorLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickening

/-!
# Finite presentation of a flat module across a first order thickening (Stacks 08W7)

Let
```
X --i--> X'
|        |
f        f'
v        v
T --t--> T'
```
be a cartesian square of algebraic spaces in which `t : T ⟶ T'` is a first order thickening, let
`ℱ'` be an `𝒪_{X'}`-module flat over `T'` and set `ℱ = i^*ℱ'`.  Stacks 08W7 says that the four
conditions
1. `ℱ'` is a quasi-coherent `𝒪_{X'}`-module of finite presentation,
2. `ℱ'` is an `𝒪_{X'}`-module of finite presentation,
3. `ℱ` is a quasi-coherent `𝒪_X`-module of finite presentation,
4. `ℱ` is an `𝒪_X`-module of finite presentation,

are equivalent.

## Main results

* `Space.isFinitePresentationOnSite_tfae_of_isPullback_of_isFirstOrderThickening`: the four
  conditions above are equivalent.

## Implementation notes

A first order thickening `t : T ⟶ T'` is a monomorphism whose range is a first order thickening of
`T'` in the sense of Stacks 05ZK (`AlgebraicGeometry.Space.IsFirstOrderThickening`).  Finite
presentation and quasi-coherence are those of the small étale ringed site
(`SheafOfModules.IsFinitePresentationOnSite`, `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL),
the ones of the objects of `Coh_{X/B}` (Stacks 08KB); flatness over `T'` is Stacks 05VV.

As in the source, (1) ⇔ (2) and (3) ⇔ (4) because a module of finite presentation is
quasi-coherent, and (2) ⇔ (4) is Stacks 08VU.  The square identifies `X` with the inverse image
`f'⁻¹(t(T))`, a first order thickening of `X'` (Stacks 09ZX); the morphism of small étale ringed
topoi of its inclusion is a first order thickening of ringed topoi
(`AlgebraicGeometry.Space.smallEtaleRingedToposHomFirstOrderThickening`), flatness over `T'`
makes the action of its ideal injective
(`AlgebraicGeometry.Space.idealTensorLocallyVanishes_of_isFlatOver`, the consequence of Stacks
08MQ that the proof of 08VU uses), and the argument of 08VU then applies
(`Deformation.ToposThickening.isFinitePresentationOnSite_of_pullbackModules_of_idealTensor`).

## References

* [Stacks Project, Tag 08W7](https://stacks.math.columbia.edu/tag/08W7)
* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The source of a cartesian square over a monomorphism `t` is the inverse image of the range of
`t`: the inclusion of that inverse image is, up to an isomorphism of algebraic spaces, the top
morphism of the square. -/
theorem exists_iso_comp_eq_subspaceInclusion_of_isPullback {T T' X X' : AlgebraicSpaces B S hS}
    (t : T ⟶ T') [Mono t.hom] (hW : IsClosedSubspace B S hS (Subfunctor.range t.hom))
    {i : X ⟶ X'} {f : X ⟶ T} {f' : X' ⟶ T'} (hsq : IsPullback i f f' t) :
    ∃ e : X ≅ ⟨(preimageSubspace B S hS f' ⟨Subfunctor.range t.hom, hW⟩).1.toFunctor,
        (preimageSubspace B S hS f' ⟨Subfunctor.range t.hom, hW⟩).2.1⟩,
      e.inv ≫ i =
        subspaceInclusion B S hS X' (preimageSubspace B S hS f' ⟨Subfunctor.range t.hom, hW⟩) := by
  have hP : IsPullback i.hom (f.hom ≫ Subfunctor.toRange t.hom) f'.hom
      (Subfunctor.range t.hom).ι :=
    (AlgebraicSpaces.isPullback_hom B S hS hsq).of_iso (Iso.refl _) (Iso.refl _)
      (asIso (Subfunctor.toRange t.hom)) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [Subfunctor.toRange_ι])
  have hW' := (Subfunctor.isPullback_fromPreimage (Subfunctor.range t.hom) f'.hom).flip
  let eP := hP.isoIsPullback _ _ hW'
  refine ⟨ObjectProperty.isoMk _ eP, ObjectProperty.hom_ext _ ?_⟩
  change eP.inv ≫ i.hom = ((Subfunctor.range t.hom).preimage f'.hom).ι
  rw [Iso.inv_comp_eq]
  exact (hP.isoIsPullback_hom_fst _ _ hW').symm

/-- **Stacks 08W7.** Let `X ⟶ X'` over `T ⟶ T'` be a cartesian square of algebraic spaces in
which `t : T ⟶ T'` is a first order thickening, let `ℱ'` be an `𝒪_{X'}`-module flat over `T'`
and set `ℱ = i^*ℱ'`.  Then the following are equivalent: (1) `ℱ'` is a quasi-coherent
`𝒪_{X'}`-module of finite presentation; (2) `ℱ'` is an `𝒪_{X'}`-module of finite presentation;
(3) `ℱ` is a quasi-coherent `𝒪_X`-module of finite presentation; (4) `ℱ` is an `𝒪_X`-module of
finite presentation. -/
@[stacks 08W7]
theorem isFinitePresentationOnSite_tfae_of_isPullback_of_isFirstOrderThickening
    {T T' X X' : AlgebraicSpaces B S hS} (t : T ⟶ T') [Mono t.hom]
    (ht : IsFirstOrderThickening B S hS T' (Subfunctor.range t.hom))
    (i : X ⟶ X') (f : X ⟶ T) (f' : X' ⟶ T') (hsq : IsPullback i f f' t)
    (F' : Modules.{u, u} B S hS X'.1 X'.2) (hflat : IsFlatOver B S hS X'.2 f'.hom F') :
    List.TFAE
      [F'.IsQuasicoherentOnSite ∧ F'.IsFinitePresentationOnSite,
        F'.IsFinitePresentationOnSite,
        ((modulePullback B S hS i).obj F').IsQuasicoherentOnSite ∧
          ((modulePullback B S hS i).obj F').IsFinitePresentationOnSite,
        ((modulePullback B S hS i).obj F').IsFinitePresentationOnSite] := by
  let ZT : ClosedSubspaces B S hS T'.1 := ⟨Subfunctor.range t.hom, ht.1.1⟩
  let Z := preimageSubspace B S hS f' ZT
  have hZ : IsFirstOrderThickening B S hS X' Z.1 :=
    isFirstOrderThickening_preimage B S hS (Subfunctor.range t.hom) f' ht
  have h24 : F'.IsFinitePresentationOnSite ↔
      ((modulePullback B S hS i).obj F').IsFinitePresentationOnSite := by
    refine ⟨isFinitePresentationOnSite_modulePullback B S hS i F', fun h => ?_⟩
    obtain ⟨e, he⟩ := exists_iso_comp_eq_subspaceInclusion_of_isPullback B S hS t ht.1.1 hsq
    have h1 : ((modulePullback B S hS (e.inv ≫ i)).obj F').IsFinitePresentationOnSite :=
      SheafOfModules.IsFinitePresentationOnSite.of_iso
        ((modulePullbackCompIso B S hS e.inv i).app F')
        (isFinitePresentationOnSite_modulePullback B S hS e.inv _ h)
    rw [he] at h1
    have : Mono (subspaceInclusion B S hS X' Z).hom := (inferInstance : Mono Z.1.ι)
    have hiso : IsIso (Subfunctor.toRange (subspaceInclusion B S hS X' Z).hom) := inferInstance
    exact Deformation.ToposThickening.isFinitePresentationOnSite_of_pullbackModules_of_idealTensor
      (smallEtaleRingedToposHomFirstOrderThickening B S hS (subspaceInclusion B S hS X' Z)
        hiso (by rwa [show Subfunctor.range (subspaceInclusion B S hS X' Z).hom = Z.1 from
          Subfunctor.range_ι Z.1])) F'
      (idealTensorLocallyVanishes_of_isFlatOver B S hS f' ZT F' hflat)
      (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _ h1)
  tfae_have 1 ↔ 2 := and_iff_right_of_imp fun _ => inferInstance
  tfae_have 3 ↔ 4 := and_iff_right_of_imp fun _ => inferInstance
  tfae_have 2 ↔ 4 := h24
  tfae_finish

end AlgebraicGeometry.Space

end
