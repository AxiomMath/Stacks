module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TrivializationTorsor

/-!
# The torsor of trivializations over the torsor of local generators

Let `C` be a site and `F : C ⥤ Scheme` a functor whose global functions form a sheaf of
commutative rings and whose units form a sheaf. A trivialization of a pair `(L, α)` on the
resulting ringed site is in particular a local generator of `L`, and the inclusion of the
trivializations into the local generators is equivariant for the inclusion `μ_n ⟶ 𝐆_m` of
coefficient sheaves: a root of unity acts on both sides by scaling by the same unit. Read
through the bijection of Tag 03AJ this says that the map `H¹(C, μ_n) ⟶ H¹(C, 𝐆_m)` carries the
class of the torsor of trivializations of `(L, α)` to the class of the torsor of local
generators of `L`, which by Tag 040E is the class of `L` in the Picard group.

This is the compatibility of the second construction of Tag 040Q with Tag 03P8, and it is what
makes the identification of Tag 040Q a map of extensions.

## Main results

* `AlgebraicGeometry.unitsAddSheaf_schemeFunctionsRingedSite`: the sheaf of units of the ringed
  site is the sheaf of units of the functor, with no comparison.
* `AlgebraicGeometry.normalizedToGenerator_rootAct`: the inclusion of the trivializations into
  the local generators is equivariant for the inclusion `μ_n ⟶ 𝐆_m`.
* `AlgebraicGeometry.trivializationTorsor_firstCohomologyMap`: **the map
  `H¹(C, μ_n) ⟶ H¹(C, 𝐆_m)` carries the class of the torsor of trivializations of `(L, α)` to
  the class of the torsor of local generators of `L`.**

## Implementation notes

Both actions are multiplication by one and the same unit: the action on the trivializations is
`AlgebraicGeometry.rootAct`, which scales by `AlgebraicGeometry.rootUnit`, and that unit is by
definition the image of the section under the inclusion `μ_n ⟶ 𝐆_m`, which is the unit acting on
the generator torsor. So the equivariance is `Subtype.ext` applied to
`AlgebraicGeometry.rootAct_val`, with no computation.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors (AbelianTorsor torsorSetoid torsorIsoClassesEquivH1)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)

universe t v u

namespace AlgebraicGeometry

section

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (hO : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)

/-- The sheaf of units of the ringed site given by a site of schemes carrying the global
functions is the sheaf of units of that functor, on the nose. -/
theorem unitsAddSheaf_schemeFunctionsRingedSite :
    unitsAddSheaf (schemeFunctionsRingedSite J F hO) = unitsSheaf J F h := rfl

variable [(schemeFunctionsRingedSite J F hO).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (schemeFunctionsRingedSite J F hO).J AddCommGrpCat.{u}]
    (hX : RingedSite.IsLocallyRinged (schemeFunctionsRingedSite J F hO))
    (hroot : LocalRoots (schemeFunctionsRingedSite J F hO) n)
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))
    (hL : IsInvertible (schemeFunctionsRingedSite J F hO).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O).2 L)
    (al : tpow (schemeFunctionsRingedSite J F hO) L n ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeFunctionsRingedSite J F hO).O))

/-- **The inclusion of the trivializations of a pair into the local generators of its invertible
module is equivariant for the inclusion `μ_n ⟶ 𝐆_m`.** -/
theorem normalizedToGenerator_rootAct (U : Cᵒᵖ)
    (a : (rootsOfUnitySheaf J F h n).obj.obj U)
    (s : (normalizedSubfunctor (schemeFunctionsRingedSite J F hO) L n al).obj U) :
    (normalizedToGenerator (schemeFunctionsRingedSite J F hO) L n al).app U
        (rootAct J F hO h n L al U a s) =
      (generatorTorsor' (schemeFunctionsRingedSite J F hO) hX L hL).torsor.1.act U
        (Multiplicative.ofAdd ((kernel.ι (powerSheaf J F h n)).hom.app U a))
        ((normalizedToGenerator (schemeFunctionsRingedSite J F hO) L n al).app U s) :=
  Subtype.ext (rootAct_val J F hO h n L al U a s)

variable [HasSheafify J AddCommGrpCat.{u}] [HasExt.{t} (Sheaf J AddCommGrpCat.{u})]

/-- **The map `H¹(C, μ_n) ⟶ H¹(C, 𝐆_m)` carries the class of the torsor of trivializations of a
pair `(L, α)` to the class of the torsor of local generators of `L`.** -/
theorem trivializationTorsor_firstCohomologyMap :
    Sheaf.H.map (kernel.ι (powerSheaf J F h n)) 1
        (torsorIsoClassesEquivH1 (rootsOfUnitySheaf J F h n)
          (Quotient.mk _ (trivializationTorsor J F hO h n hX hroot L hL al))) =
      torsorIsoClassesEquivH1 (unitsSheaf J F h)
        (Quotient.mk _
          ((generatorTorsor' (schemeFunctionsRingedSite J F hO) hX L hL).torsor :
            AbelianTorsor (unitsSheaf J F h))) :=
  Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_naturality
    (kernel.ι (powerSheaf J F h n)) (trivializationTorsor J F hO h n hX hroot L hL al)
    (generatorTorsor' (schemeFunctionsRingedSite J F hO) hX L hL).torsor
    (normalizedToGenerator (schemeFunctionsRingedSite J F hO) L n al)
    (fun U a s => normalizedToGenerator_rootAct J F hO h n hX L hL al U a s)

end

end AlgebraicGeometry

end
