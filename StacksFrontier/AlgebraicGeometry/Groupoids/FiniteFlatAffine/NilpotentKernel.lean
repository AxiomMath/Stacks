module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.IntegralInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange

/-!
# The kernel of the map to the invariant functions of a base-changed groupoid

For an affine groupoid scheme with finite locally free source and target, the canonical map
from a base ring `C'` to the ring of invariant functions of the base-changed groupoid has
locally nilpotent kernel.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isNilpotent_of_mem_ker_canonicalMapToInvariantFunctions`:
  every element of the kernel is nilpotent.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A global function on an affine scheme with a surjective morphism to `Spec C` which pulls
back to zero comes from a nilpotent element of `C`. -/
private theorem isNilpotent_of_appTop_eq_zero_of_surjective {C : Type u} [CommRing C]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (.of C)) (hg : Surjective g) (x : C)
    (hx : (((Scheme.ΓSpecIso (.of C)).inv ≫ g.appTop).hom) x = 0) : IsNilpotent x := by
  let h : C →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of C)).inv ≫ g.appTop).hom
  have hmap : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom h) = g := by
    change X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of C)).inv ≫ g.appTop) = g
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  exact mem_nilradical.mp ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical h).mp
    (Function.Surjective.of_comp (hmap ▸ hg).surj).denseRange (RingHom.mem_ker.mpr hx))

/-- Each element killed by the canonical map from the base ring to the invariant functions of the
base-changed groupoid is nilpotent. -/
@[stacks 03BK "nilpotent_kernel"]
theorem isNilpotent_of_mem_ker_canonicalMapToInvariantFunctions {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] {C' : Type u}
    [CommRing C'] [Algebra (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') (f : C')
    (hf : f ∈ RingHom.ker G'.canonicalMapToInvariantFunctions) : IsNilpotent f := by
  have : IsAffine G'.groupoid.objects.left := IsAffine.of_isIso G'.objectsIso.hom
  have hbase : Surjective (objectsToInvariantSpectrum G) := by
    change Surjective (G.objects.left.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariantRing G).subtype))
    have : Surjective (Spec.map (CommRingCat.ofHom (invariantRing G).subtype)) :=
      ⟨(isIntegral_invariantRing G).comap_surjective Subtype.val_injective⟩
    infer_instance
  exact isNilpotent_of_appTop_eq_zero_of_surjective G'.groupoid.objects.hom
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback G'.objects_isPullback hbase) f
    (congrArg Subtype.val (RingHom.mem_ker.mp hf))

end AlgebraicGeometry.GroupoidScheme

end
