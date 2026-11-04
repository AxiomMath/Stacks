module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.CokernelMultiplicity
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorRule

/-!
# The stalk of the ideal of denominators

Let `X` be a scheme, `L` a sheaf of `𝒪_X`-modules and `s` a meromorphic section of `L`. The
ideal of denominators `I` of `s` sits in `𝒪_X` by `AlgebraicGeometry.denominatorIdealι`, and the
stalk map of that inclusion lands in the local ring `𝒪_{X,x}`, once the stalk of `𝒪_X` as a
module over itself is identified with `𝒪_{X,x}` by `Stacks.Ample.unitStalkEquiv`. This file
records that composite, its value on a germ, and the resulting description of its image: an
element of `𝒪_{X,x}` is a germ of a denominator of `s` exactly when it comes from the stalk of
`I`.

The same composite computes the multiplicity of Stacks 02QX part (1) of the cokernel of any
morphism into `𝒪_X`, which for the inclusion of the denominators is the first of the two
quotients of Stacks 02SW part (1).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.unitStalkLinearMap` — the stalk map of a morphism into
  `𝒪_X`, as a linear map to the local ring.

## Main results

* `AlgebraicGeometry.Scheme.Modules.unitStalkLinearMap_germ` — it sends the germ of a section
  to the germ of its image.
* `Stacks.Chow.sheafMultiplicity_cokernel_unit` — the multiplicity of the cokernel of a
  morphism into `𝒪_X` is the length of `𝒪_{X,x}` modulo the image of that stalk map.
* `AlgebraicGeometry.exists_unitStalkLinearMap_denominatorIdealι_eq_iff` and
  `AlgebraicGeometry.range_unitStalkLinearMap_denominatorIdealι` — **the stalk of the ideal of
  denominators**: its image in `𝒪_{X,x}` consists of the germs at `x` of the denominators of
  `s` on the open neighbourhoods of `x`.

## Implementation notes

`AlgebraicGeometry.stalkLinearMap` takes its values in the stalk of the `Ab`-valued presheaf
underlying `𝒪_X` read as a module over itself, which is a colimit in `Ab`, while `𝒪_{X,x}` is a
colimit in `CommRingCat`. `Stacks.Ample.unitStalkEquiv` is the comparison, and
`Stacks.Ample.unitStalkFun_germ` is the only property of it used here; composing with it is what
makes the image an ideal-like submodule of the local ring rather than of an abelian-group stalk.

Nothing is rewritten at the scheme level: the germ formula is the composition of the two germ
formulas, and the image of a composite with a linear equivalence is the image of the first
factor pushed forward, which is `LinearMap.range_comp`. The membership statement is phrased as
an existential rather than as `r ∈ LinearMap.range _`: elaborating `LinearMap.range` demands
the module structure on the source by instance search, and the ideal of denominators is indexed
by `Stacks.Sheaves.Differentials.ringSheaf X.sheaf` rather than
`AlgebraicGeometry.Scheme.ringCatSheaf`, two spellings of the structure sheaf that instance
search does not identify.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample (unitModule unitStalkEquiv unitStalkFun_germ)

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (x : X) {F : X.Modules} (a : F ⟶ unitModule X)

/-- The stalk map at `x` of a morphism of modules into `𝒪_X`, as a linear map into the local
ring `𝒪_{X,x}`: the stalk map of `AlgebraicGeometry.stalkLinearMap`, followed by the comparison
`Stacks.Ample.unitStalkEquiv` of the stalk of `𝒪_X` as a module over itself with `𝒪_{X,x}`. -/
def unitStalkLinearMap : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (unitStalkEquiv X x).toLinearMap.comp (stalkLinearMap F (unitModule X) a x)

/-- The stalk map into the local ring sends the germ of a section to the germ of its image. -/
theorem unitStalkLinearMap_germ (U : X.Opens) (hx : x ∈ U) (m : F.presheaf.obj (op U)) :
    unitStalkLinearMap x a (F.presheaf.germ U x hx m) =
      X.presheaf.germ U x hx (show Γ(X, U) from a.val.app (op U) m) :=
  (congrArg (unitStalkEquiv X x) (stalkLinearMap_germ F (unitModule X) a U x hx m)).trans
    (unitStalkFun_germ X x U hx _)

/-- The image of the stalk map into the local ring is the image of the stalk map of `a` pushed
forward along the comparison with the local ring. -/
theorem range_unitStalkLinearMap :
    LinearMap.range (unitStalkLinearMap x a) =
      Submodule.map (unitStalkEquiv X x).toLinearMap
        (LinearMap.range (stalkLinearMap F (unitModule X) a x)) :=
  LinearMap.range_comp _ _

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

/-- **The multiplicity of the cokernel of a morphism into `𝒪_X`.** It is the length of the local
ring modulo the image of the stalk map of that morphism. For the inclusion of the ideal of
denominators of a meromorphic section this is the multiplicity of the first quotient of
Stacks 02SW part (1). -/
theorem sheafMultiplicity_cokernel_unit {X : Scheme.{u}} {F : X.Modules}
    (a : F ⟶ Stacks.Ample.unitModule X) (x : X) :
    sheafMultiplicity (cokernel a) x =
      (Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸
          LinearMap.range (Scheme.Modules.unitStalkLinearMap x a))).toNat := by
  rw [sheafMultiplicity_cokernel]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (unitStalkEquiv X x)
      (Scheme.Modules.range_unitStalkLinearMap x a).symm))

end Stacks.Chow

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (L : X.Modules) (s : MeromorphicSection X.sheaf L) (x : X)

/-- **The stalk of the ideal of denominators.** An element of the local ring `𝒪_{X,x}` comes
from the stalk of the ideal of denominators of `s` exactly when it is the germ of a denominator
of `s` on some open neighbourhood of `x`, that is, of a section `f` of `𝒪_X` there with `f s` a
section of `L`.

This is the stalk form of the denominator rule
`AlgebraicGeometry.exists_denominatorIdeal_inclusion_app_eq_iff` of Stacks 02P0: every element
of a stalk is a germ, and the stalk map sends germs to germs. -/
theorem exists_unitStalkLinearMap_denominatorIdealι_eq_iff (r : X.presheaf.stalk x) :
    (∃ m, Scheme.Modules.unitStalkLinearMap x (denominatorIdealι X L s) m = r) ↔
      ∃ (V : X.Opens) (hx : x ∈ V) (f : Γ(X, V)),
        X.presheaf.germ V x hx f = r ∧
          ∃ t : L.val.obj (op V),
            (meromorphicSectionMul X L s).val.app (op V) (show Γ(unitModule X, V) from f) =
              (toMeromorphicSectionSheafAsModule X L).val.app (op V) t := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨V, hx, d, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (Scheme.Modules.presheaf (denominatorIdeal X L s)) m
    refine ⟨V, hx, (denominatorIdealι X L s).val.app (op V) d, ?_, ?_⟩
    · exact (Scheme.Modules.unitStalkLinearMap_germ x _ V hx d).symm.trans hm
    · exact (exists_denominatorIdeal_inclusion_app_eq_iff X L s V _).mp ⟨d, rfl⟩
  · rintro ⟨V, hx, f, hf, t, ht⟩
    obtain ⟨d, hd⟩ := (exists_denominatorIdeal_inclusion_app_eq_iff X L s V f).mpr ⟨t, ht⟩
    exact ⟨(Scheme.Modules.presheaf (denominatorIdeal X L s)).germ V x hx d,
      (Scheme.Modules.unitStalkLinearMap_germ x _ V hx d).trans
        ((congrArg (X.presheaf.germ V x hx) hd).trans hf)⟩

/-- **The stalk of the ideal of denominators, as a subset of the local ring.** It is the set of
germs at `x` of the denominators of `s` on the open neighbourhoods of `x`. -/
theorem range_unitStalkLinearMap_denominatorIdealι :
    Set.range (Scheme.Modules.unitStalkLinearMap x (denominatorIdealι X L s)) =
      {r | ∃ (V : X.Opens) (hx : x ∈ V) (f : Γ(X, V)),
        X.presheaf.germ V x hx f = r ∧
          ∃ t : L.val.obj (op V),
            (meromorphicSectionMul X L s).val.app (op V) (show Γ(unitModule X, V) from f) =
              (toMeromorphicSectionSheafAsModule X L).val.app (op V) t} :=
  Set.ext fun r => exists_unitStalkLinearMap_denominatorIdealι_eq_iff X L s x r

end AlgebraicGeometry
