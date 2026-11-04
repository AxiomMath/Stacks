module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along an integral morphism of schemes

Let `f : X ⟶ Y` be an integral morphism of schemes — a finite morphism, for instance, since
finiteness implies integrality. Direct image of abelian sheaves on the small étale sites is
then an exact functor, so all of its positive right derived functors vanish: an integral
morphism is acyclic for étale cohomology.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom`:
  `R^q f_* F = 0` for every abelian sheaf `F` on the small étale site of `X` and every `q ≥ 1`.

## Implementation notes

Exactness of direct image is
`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom` (Tag 04C2). Applying an
exact functor degreewise to an injective resolution gives a resolution again, so the homology of
the image complex vanishes in positive degrees; that step is
`Stacks.RightDerivedTransport.isZero_rightDerived_succ_of_preservesHomology`. Preservation of
homology is assembled here from left exactness, which direct image has as a right adjoint, and
preservation of epimorphisms, which is where integrality enters.

Enough injectives on the source, needed for the right derived functors to be computed by
resolutions, is `Stacks.EtaleCohomology.smallEtaleAbSheaf_enoughInjectives`.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **The positive higher direct images along an integral morphism vanish.** For a finite
morphism this is the acyclicity half of Stacks Project Tag 03QP, finiteness implying
integrality. -/
@[stacks 03QP "part (2): vanishing of the positive higher direct images",
  sga "4 Vbis 4.3.4",
  sga "4½ Arcata 2.3.6"]
public theorem isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero (((smallEtalePushforwardAb f).rightDerived q).obj F) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hra : (smallEtalePushforwardAb f).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb f⟩⟩
  have hfl : PreservesFiniteLimits (smallEtalePushforwardAb f) := inferInstance
  have hepi : (smallEtalePushforwardAb f).PreservesEpimorphisms :=
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom f
  have hhom := Functor.preservesHomology_of_preservesEpis_and_kernels (smallEtalePushforwardAb f)
  exact Stacks.RightDerivedTransport.isZero_rightDerived_succ_of_preservesHomology _ n F

end Stacks.EtaleCohomology

end
