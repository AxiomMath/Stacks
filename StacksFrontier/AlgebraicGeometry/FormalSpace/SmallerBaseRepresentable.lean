module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# Representable morphisms and étale-local properties over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`, and let `G` be a presheaf with values in
`Type (u + 1)` on the big fppf site of `V`, with attached presheaf
`AlgebraicGeometry.FormalSpace.smallerBaseULift` on the big fppf site of `S` (Stacks 04SG). This
file shows that a morphism over `V` which is representable with represented base changes having
a property of morphisms of schemes keeps that property over `S`, and that a presheaf over `V`
with an étale-local property of schemes keeps it over `S`. These are the properties making up a
reduction of a formal algebraic space, apart from its universal property.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_smallerBaseULiftMap`: a relative property of a
  morphism over `V` holds for the attached morphism over `S`.
* `AlgebraicGeometry.FormalSpace.hasEtaleLocalPropertyULift_smallerBaseULift`: an étale-local
  property of a presheaf over `V` holds for the attached presheaf over `S`.
* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeULift_terminal_from_of_smallerBaseULiftHom`:
  a presheaf over `V` whose attached presheaf is locally of finite type over `V` is locally of
  finite type over `V`.

## Implementation notes

Every chart of an attached presheaf is an attached chart up to an isomorphism of the site
(`AlgebraicGeometry.FormalSpace.exists_smallerBaseChart`), and the attached presheaf preserves
fibre products, so a represented base change over `S` is the attached base change over `V`, with
the same underlying morphism of schemes.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- **A relative property of morphisms does not get lost under the change of base.** If every
represented base change of a morphism `k` of presheaves on the big fppf site of `V` has a
property `Q` of morphisms of schemes, then so does every represented base change of the
attached morphism on the big fppf site of `S`. -/
theorem relative_smallerBaseULiftMap (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q] {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (k : G ⟶ G')
    (hk : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
      uliftYoneda.{u + 1} k) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative
      uliftYoneda.{u + 1} (smallerBaseULiftMap B V S hV hS g k) := by
  refine MorphismProperty.relative.of_exists (F := uliftYoneda.{u + 1}) fun U ξ => ?_
  obtain ⟨ψ, hψ, ξ₀, rfl⟩ := exists_smallerBaseChart B V S hV hS g U ξ
  set T₀ := hk.1.pullback ξ₀
  set r₀ := hk.1.snd ξ₀
  set ι := relocalizeBaseHom B V S hV hS g hψ
  refine ⟨(Over.map g).obj T₀,
    (smallerBaseULiftYonedaIso B V S hV hS g T₀).inv ≫
      smallerBaseULiftMap B V S hV hS g (hk.1.fst ξ₀),
    (Over.map g).map r₀ ≫ inv ι, ?_, ?_⟩
  · refine (isPullback_smallerBaseULiftMap B V S hV hS g (hk.1.isPullback ξ₀)).of_iso
      (smallerBaseULiftYonedaIso B V S hV hS g T₀) (Iso.refl _)
      (smallerBaseULiftYonedaIso B V S hV hS g _ ≪≫
        (uliftYoneda.{u + 1}.mapIso (asIso ι)).symm) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv, Functor.map_comp,
        Functor.map_inv]
      rw [← Category.assoc, smallerBaseULiftYonedaIso_hom_naturality B V S hV hS g r₀,
        Category.assoc]
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_inv, asIso_inv, Functor.map_inv, smallerBaseChart, Category.assoc,
        IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  · exact MorphismProperty.RespectsIso.postcomp Q
      ((BigFppfOver.toScheme B S hS).map (inv ι))
      ((BigFppfOver.toScheme B S hS).map ((Over.map g).map r₀)) (hk.property_snd ξ₀)

/-- **An étale-local property of a presheaf does not get lost under the change of base.** If a
presheaf on the big fppf site of `V` has a surjective étale atlas by a scheme with an étale-local
property `P`, then so does the attached presheaf on the big fppf site of `S`: the attached chart
of the atlas is again surjective and étale, and has the same underlying scheme. -/
theorem hasEtaleLocalPropertyULift_smallerBaseULift (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (hG : Space.HasEtaleLocalPropertyULift.{u + 1} B V hV G P) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (smallerBaseULift B V S hV hS g G) P := by
  obtain ⟨U₀, f, hsurj, het, hP⟩ := hG
  exact ⟨(Over.map g).obj U₀, smallerBaseChart B V S hV hS g f,
    (relative_smallerBaseChart_iff B V S hV hS g _ f).2 hsurj,
    (relative_smallerBaseChart_iff B V S hV hS g _ f).2 het, hP⟩

/-- The structural morphism of the presheaf attached to the terminal presheaf on the big fppf
site of `V` is an isomorphism onto the universe-lifted representable presheaf of `g : V ⟶ S`:
the equivalence of Stacks 04SG sends the terminal object to the terminal object of the slice
category, which is the identity of that representable presheaf. -/
theorem isIso_smallerBaseULiftHom_terminal :
    IsIso (smallerBaseULiftHom B V S hV hS g (⊤_ ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)))) := by
  let Φ := smallerBasePresheafEquivalenceULift B V S hV hS g
  let e := (terminalIsTerminal.isTerminalObj Φ.functor _).uniqueUpToIso Over.mkIdTerminal
  have hw : (Φ.functor.obj (⊤_ ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)))).hom = e.hom.left := by
    simpa using (Over.w e.hom).symm
  change IsIso (Φ.functor.obj (⊤_ ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)))).hom
  rw [hw]
  exact (Over.forget _).map_isIso e.hom

/-- **Local finite type over a smaller base, for large-valued presheaves.** A presheaf `G` with
values in `Type (u + 1)` on the big fppf site of `V` is locally of finite type over `V` as soon as
the structural morphism of the attached presheaf on the big fppf site of `S` to `V` is. -/
theorem isLocallyOfFiniteTypeULift_terminal_from_of_smallerBaseULiftHom
    {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (hG : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (smallerBaseULiftHom B V S hV hS g G)) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B V hV (terminal.from G) := by
  have := isIso_smallerBaseULiftHom_terminal B V S hV hS g
  refine (isLocallyOfFiniteTypeULift_smallerBaseULiftMap_iff B V S hV hS g _).mp ?_
  have heq : smallerBaseULiftMap B V S hV hS g (terminal.from G) =
      smallerBaseULiftHom B V S hV hS g G ≫
        inv (smallerBaseULiftHom B V S hV hS g (⊤_ ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)))) := by
    rw [IsIso.eq_comp_inv, smallerBaseULiftMap_comp_hom]
  rw [heq]
  exact Space.holdsOnEveryEtaleChartULift_postcomp B S hS _ _ _ hG

end AlgebraicGeometry.FormalSpace

end
