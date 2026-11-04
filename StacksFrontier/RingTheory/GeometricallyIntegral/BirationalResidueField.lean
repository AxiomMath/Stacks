module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapReduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericStalkCriterion

/-!
# Birationality over a base, tested on the generic residue fields

Stacks 0552 says: for integral schemes `X` and `Y` locally of finite type over a base `S` with
generic points `x` and `y`, the following are equivalent: (1) `X` and `Y` are `S`-birational,
(2) some nonempty opens of `X` and `Y` are `S`-isomorphic, and (3) `x` and `y` have the same
image `s` in `S` and `κ(x) ≅ κ(y)` as `κ(s)`-extensions.

Parts (1) and (2) are already equivalent without any finiteness hypothesis, by
`AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso`. This file proves the
equivalence of (1) and (3), which is the content that the first proof of Stacks 0559 applies:
there one has a presentation `B' = A[x_1, …, x_{r+1}]/(P)` whose fraction field is `κ(x)` as a
`κ(η)`-extension, and one needs a `Y`-isomorphism between nonempty opens of `X` and of
`Spec B'`.

## Main results

* `AlgebraicGeometry.birationalOver_iff_generic_residueField_iso` is the equivalence of parts
  (1) and (3) of Stacks 0552.

## Implementation notes

Unlike `AlgebraicGeometry.birationalOver_iff_generic_stalk_iso` (Stacks 0BAD, parts (1) and
(3)), which asks for finite presentation and compares the local rings, this statement asks only
for finite type and compares the residue fields. The two agree here because `X` and `Y` are
integral, so the local ring at the generic point is already a field and the residue map is an
isomorphism: that is Stacks 00EU in the form `IsLocalRing.maximalIdeal_eq_bot`.

The forward implication is the already-proved
`AlgebraicGeometry.residueFieldIso_of_birationalOver`. The reverse implication turns the given
residue-field isomorphism into local data at the generic point, invokes surjectivity of the
generic-point map for rational maps over the base
(`AlgebraicGeometry.GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_isReduced`,
Stacks 0BX8) to realize that data by a rational map, and then applies Stacks 0BAC
(`AlgebraicGeometry.birationalOver_of_isBirational`) to a partial map representing it. The
finite type hypothesis enters twice: `Y` locally of finite type over `S` is what 0BX8 needs,
and `X` locally of finite type over `S` is what makes the representing morphism locally of
finite type so that 0BAC applies with `Y` reduced.

An isomorphism of residue fields is required to commute with the two maps from the residue
field of the common image in `S`. Transport along the equality of those image points identifies
that base residue field, which is why the statement binds the equality `h` and then casts along
it.

The scaffolding before the main theorem is imported from
`StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericResidueField`. The natural home of
this module is `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/`, next to the rest of its
dependencies.

## References

* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0552, parts (1) and (3).** Birationality over a base of two integral schemes
locally of finite type over it is equivalent to their generic points having the same image in
the base together with an isomorphism of their residue fields at those generic points over the
residue field of that common image. -/
@[stacks 0552 "parts (1) and (3)"]
theorem birationalOver_iff_generic_residueField_iso
    {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] :
    Scheme.BirationalOver sX sY ↔
      ∃ (h : sX (genericPoint X) = sY (genericPoint Y))
        (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y)),
        h ▸ (sX.residueFieldMap (genericPoint X) ≫ e.hom) =
          sY.residueFieldMap (genericPoint Y) := by
  constructor
  · exact residueFieldIso_of_birationalOver sX sY
  · rintro ⟨h, e, he⟩
    classical
    let C := genericPointContext sX sY
    let i : Fin C.numberOfComponents := ⟨0, by simp [C]⟩
    have : IsIntegral C.X := inferInstanceAs (IsIntegral X)
    let eStalk := genericStalkResidueFieldIso X ≪≫ e ≪≫ (genericStalkResidueFieldIso Y).symm
    let d : C.GenericPointLocalMap i := by
      simpa [C, i, genericPointContext] using genericPointLocalMapOfResidueFieldIso sX sY h e he
    have hdIso : IsIso d.stalkMap := by
      show IsIso eStalk.inv
      infer_instance
    let data : ∀ j, C.GenericPointLocalMap j := fun j => by
      have hj : j = i := by
        apply Fin.ext
        simp only [i, C, genericPointContext] at *
        omega
      exact hj ▸ d
    have : LocallyOfFiniteType C.toBaseTarget := inferInstanceAs (LocallyOfFiniteType sY)
    have : IsReduced C.X := inferInstanceAs (IsReduced X)
    obtain ⟨f, hfdata⟩ :=
      (GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_isReduced C).surjective
        data
    let : C.X.Over S := ⟨C.toBaseSource⟩
    let : C.Y.Over S := ⟨C.toBaseTarget⟩
    have : f.1.IsOver S := Scheme.RationalMap.isOver_iff.mpr f.2
    obtain ⟨g, hgOver, hg⟩ := f.1.exists_partialMap_over S
    have hOver : g.hom ≫ sY = g.domain.ι ≫ sX := Scheme.PartialMap.isOver_iff.mp hgOver
    let z : g.domain := ⟨genericPoint X, genericPoint_mem_dense_open g.domain g.dense_domain⟩
    have : Nonempty g.domain.toScheme := ⟨z⟩
    have : IsIntegral g.domain.toScheme := isIntegral_of_isOpenImmersion g.domain.ι
    have : IsIntegral C.Y := inferInstanceAs (IsIntegral Y)
    have hpointMap := C.genericPointMapForRationalMaps.map_point f g hg hOver
      (fun _ => genericPoint_mem_dense_open g.domain g.dense_domain) i
    have hdatai : C.genericPointMapForRationalMaps f i = d := by
      simpa [data, C, genericPointContext] using congrFun hfdata i
    have hdataPair := Sigma.mk.inj_iff.mp (congrArg
      (fun q : C.GenericPointLocalMap i =>
        (⟨q.point, q.stalkMap⟩ :
          Σ y : C.Y, C.Y.presheaf.stalk y ⟶ C.X.presheaf.stalk (C.genericPoint i))) hdatai)
    have hdPoint : d.point = genericPoint C.Y := by
      dsimp [d, genericPointLocalMapOfResidueFieldIso]
    change (C.genericPointMapForRationalMaps f i).point = g.hom z at hpointMap
    have hpoint : g.hom z = genericPoint Y := by
      simpa [C, genericPointContext] using hpointMap.symm.trans (hdataPair.1.trans hdPoint)
    have hstalkMap := C.genericPointMapForRationalMaps.map_stalk f g hg hOver
      (fun _ => genericPoint_mem_dense_open g.domain g.dense_domain) i
    have hstalkEq := stalkMap_eq_of_heq hpoint.symm (hdataPair.2.symm.trans hstalkMap)
    have : IsIso (eqToHom (congrArg Y.presheaf.stalk hpoint.symm) ≫
        (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom)) := hstalkEq.symm ▸ hdIso
    have : IsIso (g.hom.stalkMap z ≫ (g.domain.stalkIso z).hom) :=
      IsIso.of_isIso_comp_left (eqToHom (congrArg Y.presheaf.stalk hpoint.symm)) _
    have hgStalk : IsIso (g.hom.stalkMap z) :=
      IsIso.of_isIso_comp_right _ (g.domain.stalkIso z).hom
    have hz : z = genericPoint g.domain.toScheme :=
      Subtype.ext (genericPoint_eq_of_isOpenImmersion g.domain.ι).symm
    have hBirational : IsBirational g.hom := by
      apply isBirational_of_bijOn_of_isIso_stalkMap
      · rwa [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton, ← hz]
      · intro x hx
        rw [genericPoints_eq_singleton] at hx
        subst x
        rw [← hz]
        exact hgStalk
    have : Finite (irreducibleComponents g.domain.toScheme) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have : Finite (irreducibleComponents Y) := by
      rw [irreducibleComponents_eq_singleton]
      infer_instance
    have : LocallyOfFiniteType (g.hom ≫ sY) := by
      rw [hOver]
      infer_instance
    have hgLFT : LocallyOfFiniteType g.hom := locallyOfFiniteType_of_comp g.hom sY
    exact (g.domain.birationalOver_of_dense sX g.dense_domain).symm.trans
      (birationalOver_of_isBirational (g.domain.ι ≫ sX) sY g.hom hBirational hOver
        (Or.inl ⟨hgLFT, inferInstance⟩))

add_to_stacks 0552 "parts (1) and (2)"
  AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso

end AlgebraicGeometry

end
