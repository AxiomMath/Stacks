module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistenceUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.LowerShriekHomMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.SheafyTrace

/-!
# The sheafy trace map on étale derived categories

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `f = f̄ ∘ j` (an open immersion
`j : X ⟶ X̄` followed by a proper morphism `f̄ : X̄ ⟶ Y`), let `Λ` be a commutative ring, and
suppose that the derived lower shriek `Rf_! = Rf̄_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` has a
right adjoint `Rf^!`. For `L` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)` there is a canonical
map

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`,

the composite

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, Rf_!Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`

of the canonical map of [Stacks, Tag 0GL7] (`Stacks.EtaleCohomology.etaleLowerShriekHomMap`) at
`(L, Rf^!K)` with the internal Hom of the counit `Rf_!Rf^!K ⟶ K` of the adjunction. This is the
map of [Stacks, Tag 0GLB].

When `Λ` is a torsion ring, `Rf_!` has a right adjoint for every compactification, by
[Stacks, Tag 0G2C] (`Stacks.EtaleCohomology.isLeftAdjoint_derivedLowerShriekUnbounded`), and the
map is the one of [Stacks, Tag 0GLB] for
`Rf^! = Stacks.EtaleCohomology.derivedUpperShriekUnbounded`. If `f : X ⟶ Y` is separated of
finite type between quasi-compact and quasi-separated schemes, a compactification exists,
[Stacks, Tag 0F41]
(`AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`).

## Main definitions

* `Stacks.EtaleCohomology.etaleSheafyTrace`: the map `Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`,
  for `Rf^!` the right adjoint of `Rf_!`.
* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace`: [Stacks, Tag 0GLB], the map
  for a torsion ring `Λ`, with `Rf^!` the right adjoint of [Stacks, Tag 0G2C].

## Main results

* `Stacks.EtaleCohomology.etaleSheafyTrace_eq`: the defining composite.
* `Stacks.EtaleCohomology.etaleSheafyTrace_eq_sheafyTrace`: the map is Leray `Rf_* ≅ Rf̄_*Rj_*`
  followed by `Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData.sheafyTrace` of the
  compactification data `Stacks.EtaleCohomology.etaleCompactificationData` and the adjunction
  `Rf_! ⊣ Rf^!`.
* `Stacks.EtaleCohomology.etaleSheafyTrace_naturality_target` and
  `Stacks.EtaleCohomology.etaleSheafyTrace_naturality_source`: the map is covariant in `K` and
  contravariant in `L`.
* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace_eq`: the defining composite of
  [Stacks, Tag 0GLB], through the counit of `Rf_! ⊣ Rf^!`.

## Implementation notes

In `Stacks.EtaleCohomology.etaleSheafyTrace` that `Rf_!` is a left adjoint is an instance
argument: the construction uses nothing but the adjunction, which is the one
`Functor.IsLeftAdjoint` determines, `CategoryTheory.Adjunction.ofIsLeftAdjoint`, with `Rf^!` the
chosen right adjoint `CategoryTheory.Functor.rightAdjoint`. The source states the construction
for `f` separated of finite type between quasi-compact and quasi-separated schemes and `Λ` a
torsion ring, where the right adjoint exists by [Stacks, Tag 0G2C];
`Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace` is the construction there, the
instance being supplied by [Stacks, Tag 0G2C].

As `Rf_!` itself ([Stacks, Tag 0F7H], `Stacks.EtaleCohomology.derivedLowerShriekUnbounded`) and
the map of [Stacks, Tag 0GL7], the map is built from a compactification `f = f̄ ∘ j`, which is an
argument. It exists for every compactification, and no hypothesis on `f` beyond having one is
used; for `f` separated of finite type between quasi-compact and quasi-separated schemes one
exists by [Stacks, Tag 0F41].

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, on which
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` and the derived internal Hom
`Stacks.EtaleCohomology.etaleDerivedHom` are defined; it is named in the statements by `letI`.

## References

* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0GL7](https://stacks.math.columbia.edu/tag/0GL7)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology

variable {Λ : Type r} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

section LeftAdjoint

variable (Λ) [(derivedLowerShriekUnbounded.{u, r} f j Λ).IsLeftAdjoint]

/-- **The sheafy trace map** `Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)` on étale derived
categories, for `Rf_! = Rf̄_* ∘ j_!` computed through the compactification `j` and `Rf^!` its
right adjoint: the canonical map of [Stacks, Tag 0GL7] at `(L, Rf^!K)` followed by the internal
Hom of the counit `Rf_!Rf^!K ⟶ K`. -/
def etaleSheafyTrace
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
        (((etaleDerivedHom.{u, r} Λ X).obj (op L)).obj
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K)) ⟶
      ((etaleDerivedHom.{u, r} Λ Y).obj (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).obj
        K :=
  etaleLowerShriekHomMap.{u, r} Λ f j L
      ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K) ≫
    ((etaleDerivedHom.{u, r} Λ Y).obj (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).map
      ((Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.app K)

/-- **The defining composite of the sheafy trace map**: the canonical map of [Stacks, Tag 0GL7]
followed by the internal Hom of the counit of `Rf_! ⊣ Rf^!`. -/
theorem etaleSheafyTrace_eq
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    etaleSheafyTrace.{u, r} Λ f j L K =
      etaleLowerShriekHomMap.{u, r} Λ f j L
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K) ≫
        ((etaleDerivedHom.{u, r} Λ Y).obj
            (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).map
          ((Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.app K) :=
  rfl

/-- **The sheafy trace map through the compactification data**: it is Leray
`Rf_* ≅ Rf̄_* ∘ Rj_*` followed by
`Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData.sheafyTrace` of the étale
compactification data and the adjunction `Rf_! ⊣ Rf^!`. -/
theorem etaleSheafyTrace_eq_sheafyTrace
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    etaleSheafyTrace.{u, r} Λ f j L K =
      (etaleCompactificationLerayIso.{u, r} Λ f j).hom.app _ ≫
        (etaleCompactificationData.{u, r} Λ f j).sheafyTrace
          (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)) L K :=
  Category.assoc _ _ _

/-- **The sheafy trace map is covariant in `K`.** -/
theorem etaleSheafyTrace_naturality_target
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    {K K' : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)} (k : K ⟶ K') :
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).map
        (((etaleDerivedHom.{u, r} Λ X).obj (op L)).map
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.map k)) ≫
        etaleSheafyTrace.{u, r} Λ f j L K' =
      etaleSheafyTrace.{u, r} Λ f j L K ≫
        ((etaleDerivedHom.{u, r} Λ Y).obj
          (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).map k := by
  have hα := etaleLowerShriekHomMap_naturality_target.{u, r} Λ f j L
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.map k)
  have hc : (derivedLowerShriekUnbounded.{u, r} f j Λ).map
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.map k) ≫
        (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.app K' =
      (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.app K ≫ k :=
    (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.naturality k
  rw [etaleSheafyTrace_eq, etaleSheafyTrace_eq, ← Category.assoc, hα, Category.assoc,
    Category.assoc, ← Functor.map_comp, hc, Functor.map_comp]

/-- **The sheafy trace map is contravariant in `L`.** -/
theorem etaleSheafyTrace_naturality_source
    {L L' : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X)} (l : L' ⟶ L)
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).map
        (((etaleDerivedHom.{u, r} Λ X).map l.op).app
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K)) ≫
        etaleSheafyTrace.{u, r} Λ f j L' K =
      etaleSheafyTrace.{u, r} Λ f j L K ≫
        ((etaleDerivedHom.{u, r} Λ Y).map
          ((derivedLowerShriekUnbounded.{u, r} f j Λ).map l).op).app K := by
  have hα := etaleLowerShriekHomMap_naturality_source.{u, r} Λ f j l
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K)
  have hH := ((etaleDerivedHom.{u, r} Λ Y).map
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).map l).op).naturality
      ((Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).counit.app K)
  rw [etaleSheafyTrace_eq, etaleSheafyTrace_eq, ← Category.assoc, hα, Category.assoc,
    Category.assoc]
  exact congrArg (etaleLowerShriekHomMap.{u, r} Λ f j L
    ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K) ≫ ·) hH.symm

end LeftAdjoint

/-! ### The map of [Stacks, Tag 0GLB] for a torsion ring -/

section Torsion

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- Let `Λ` be a torsion ring and let `f : X ⟶ Y` be a morphism of schemes with a
compactification `f = f̄ ∘ j`, so that `Rf_! = Rf̄_* ∘ Rj_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)`
has the right adjoint `Rf^!` of [Stacks, Tag 0G2C]. For every `K` in `D(Y_étale, Λ)` and `L` in
`D(X_étale, Λ)` this is the canonical map

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`,

the composite `Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, Rf_!Rf^!K) ⟶ RHom_Λ(Rf_!L, K)` of the map of
[Stacks, Tag 0GL7] and the counit `Rf_!Rf^!K ⟶ K` of the adjunction
(`Stacks.EtaleCohomology.derivedUpperShriekUnboundedSheafyTrace_eq`).

A compactification exists when `f` is separated of finite type between quasi-compact and
quasi-separated schemes, [Stacks, Tag 0F41]. -/
@[stacks 0GLB]
def derivedUpperShriekUnboundedSheafyTrace
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
    letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
        (((etaleDerivedHom.{u, r} Λ X).obj (op L)).obj
          ((derivedUpperShriekUnbounded.{u, r} Λ j hΛ).obj K)) ⟶
      ((etaleDerivedHom.{u, r} Λ Y).obj (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).obj
        K :=
  haveI := isLeftAdjoint_derivedLowerShriekUnbounded.{u, r} Λ j hΛ
  etaleSheafyTrace.{u, r} Λ f j L K

/-- **The defining composite of [Stacks, Tag 0GLB]**: the map of [Stacks, Tag 0GL7] at
`(L, Rf^!K)` followed by the internal Hom of the counit `Rf_!Rf^!K ⟶ K` of the adjunction
`Rf_! ⊣ Rf^!` of [Stacks, Tag 0G2C]. -/
theorem derivedUpperShriekUnboundedSheafyTrace_eq
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    derivedUpperShriekUnboundedSheafyTrace.{u, r} f j hΛ L K =
      etaleLowerShriekHomMap.{u, r} Λ f j L ((derivedUpperShriekUnbounded.{u, r} Λ j hΛ).obj K) ≫
        ((etaleDerivedHom.{u, r} Λ Y).obj
            (op ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj L))).map
          ((derivedLowerShriekUnboundedAdjunction.{u, r} Λ j hΛ).counit.app K) :=
  rfl

/-- The map of [Stacks, Tag 0GLB] for a torsion ring is `Stacks.EtaleCohomology.etaleSheafyTrace`
for the left adjoint `Rf_!` of [Stacks, Tag 0G2C]. -/
theorem derivedUpperShriekUnboundedSheafyTrace_eq_etaleSheafyTrace
    (L : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ X)
      DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : letI := HasDerivedCategory.standard (EtaleModules.{u, r} Λ Y)
      DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    haveI := isLeftAdjoint_derivedLowerShriekUnbounded.{u, r} Λ j hΛ
    derivedUpperShriekUnboundedSheafyTrace.{u, r} f j hΛ L K = etaleSheafyTrace.{u, r} Λ f j L K :=
  rfl

end Torsion

end Stacks.EtaleCohomology

end
