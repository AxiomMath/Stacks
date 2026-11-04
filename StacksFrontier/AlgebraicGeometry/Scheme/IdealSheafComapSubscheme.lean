module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed subscheme cut out by the restriction of an ideal sheaf to an open

Let `I` be a quasi-coherent sheaf of ideals on a scheme `S` and let `V` be an open subscheme of
`S`. The closed subscheme of `V` cut out by the inverse image `I.comap V.ι` is the part of the
closed subscheme of `S` cut out by `I` lying over `V`, namely the open subscheme
`I.subschemeι ⁻¹ᵁ V` of `I.subscheme`.

Mathlib has `AlgebraicGeometry.Scheme.IdealSheafData.comapIso`, which presents
`(I.comap f).subscheme` as the fibre product `V ×_S I.subscheme` for an arbitrary `f`; for an
open immersion the fibre product is an open subscheme of the second factor, which is
`AlgebraicGeometry.pullbackRestrictIsoRestrict`. This file composes the two in the form an ideal
sheaf is usually met in.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_subschemeIso_resLE` — for a closed immersion
  `i : Y ⟶ X`, an open `U` of `X` and an ideal sheaf on `U` *known* to be `i.ker.comap U.ι`, the
  closed subscheme it cuts out is the open `i ⁻¹ᵁ U` of `Y`, compatibly with the closed
  immersion and with `AlgebraicGeometry.Scheme.Hom.resLE` of `i`. Without that compatibility
  square the isomorphism would say nothing about *which* closed subscheme of `U` it identifies.

## Implementation notes

`exists_subschemeIso_resLE` is phrased as an existential over a hypothesis
`J = i.ker.comap V.ι` and proved by `subst`, as
`Stacks.CartierQuotientChart.exists_subschemeIsoSpec_of_ideal_eq` is: transporting the
isomorphism along that equation with `▸` would leave a definition whose `hom` no rewrite can see
through. It is also what keeps the statement usable when `J` and `i.ker` are spelled over scheme
terms that are equal only by `rfl`: the equation is discharged once, by the lemma supplying it,
instead of inside a goal mentioning both spellings.

The composite identification `(I.comap V.ι).subscheme ≅ (I.subschemeι ⁻¹ᵁ V).toScheme` and the
square pinning it against the two closed immersions into `S` are built inside the proof rather
than as declarations of their own.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **The closed subscheme of an open `U` cut out by the restriction of the kernel of a closed
immersion `i : Y ⟶ X` is the open `V = i ⁻¹ U` of `Y`**, compatibly with the two morphisms to
`U`: the closed immersion cut out by the restricted ideal sheaf and the restriction of `i`
itself. -/
@[ega "I 4.1.4" "partial"]
theorem exists_subschemeIso_resLE {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    {U : X.Opens} {V : Y.Opens} (hV : i ⁻¹ᵁ U = V) {J : U.toScheme.IdealSheafData}
    (hJ : J = i.ker.comap U.ι) :
    ∃ e : J.subscheme ≅ V.toScheme, e.hom ≫ i.resLE U V hV.ge = J.subschemeι := by
  subst hJ
  set e₀ : (i.ker.comap U.ι).subscheme ≅ (i.ker.subschemeι ⁻¹ᵁ U).toScheme :=
    i.ker.comapIso U.ι ≪≫ pullbackSymmetry _ _ ≪≫
      pullbackRestrictIsoRestrict i.ker.subschemeι U with he₀
  have hι : e₀.hom ≫ (i.ker.subschemeι ⁻¹ᵁ U).ι =
      (i.ker.comapIso U.ι).hom ≫ pullback.snd _ _ := by
    rw [he₀]; simp
  have hιsub : e₀.hom ≫ (i.ker.subschemeι ⁻¹ᵁ U).ι ≫ i.ker.subschemeι =
      (i.ker.comap U.ι).subschemeι ≫ U.ι := by
    rw [← Category.assoc, hι, Category.assoc, ← pullback.condition, ← Category.assoc,
      comapIso_hom_fst]
  have hinv : (asIso i.toImage).inv ≫ i = i.ker.subschemeι :=
    (Iso.inv_comp_eq _).mpr i.toImage_imageι.symm
  have hopen : i.ker.subschemeι ⁻¹ᵁ U = (asIso i.toImage).inv ⁻¹ᵁ V := by
    rw [← hV, ← Scheme.Hom.comp_preimage, hinv]
  refine ⟨e₀ ≪≫ i.ker.subscheme.isoOfEq hopen ≪≫ asIso ((asIso i.toImage).inv ∣_ V), ?_⟩
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, morphismRestrict_ι_assoc, hinv,
    Scheme.isoOfEq_hom_ι_assoc, hιsub]

end AlgebraicGeometry.Scheme.IdealSheafData

end
