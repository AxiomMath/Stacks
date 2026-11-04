module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Functoriality of the quotient sheaf of a pre-relation

A morphism of pre-relations induces a map of quotient sheaves, and
`Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap` says that this map is compatible
with the canonical projections. Since the projection onto the quotient sheaf is an epimorphism
of presheaves followed by sheafification, that compatibility determines the induced map; this
file records the consequences one needs in practice.

## Main results

* `Stacks.Groupoids.isLocallySurjective_sheafifyMap_toQuotientPresheaf`: the sheafification of
  the projection onto the quotient presheaf is a locally surjective map of sheaves, and
  `Stacks.Groupoids.toSheafify_comp_sheafifyMap_toQuotientPresheaf` identifies its composite
  with the sheafification map as the projection onto the quotient sheaf.

## Implementation notes

The site is presented by an arbitrary functor `F : C ⥤ Over S` into `S`-schemes, which covers
the big and small Zariski, étale, fppf, smooth and syntomic sites at once.

The quotient sheaf is the sheafification of a coequalizer of presheaves of types. The
projection onto the quotient presheaf is a coequalizer projection, hence an epimorphism, and
sheafification is a left adjoint, hence preserves epimorphisms; this is why the sheafified
projection is locally surjective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]
variable (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)

/-- Sheafifying the projection onto the quotient presheaf and precomposing with the
sheafification map recovers the projection onto the quotient sheaf. -/
theorem toSheafify_comp_sheafifyMap_toQuotientPresheaf {R U : Over S} (j : PreRelation R U) :
    toSheafify J (points F U) ≫ sheafifyMap J (toQuotientPresheaf F j) =
      toQuotientSheaf J F j :=
  (toSheafify_naturality J (toQuotientPresheaf F j)).symm

/-- The sheafification of the projection onto the quotient presheaf is a locally surjective
map of sheaves. -/
theorem isLocallySurjective_sheafifyMap_toQuotientPresheaf {R U : Over S}
    (j : PreRelation R U) :
    Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map (toQuotientPresheaf F j)) := by
  rw [Sheaf.isLocallySurjective_iff_epi]
  let _ : Epi (toQuotientPresheaf F j) := inferInstance
  infer_instance

end Stacks.Groupoids

end
