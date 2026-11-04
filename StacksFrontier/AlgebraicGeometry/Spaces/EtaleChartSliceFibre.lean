module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# The étale-chart condition for the slice fibre of a morphism to a representable presheaf

Let `V` be an object of the big fppf site of a scheme `S` and let `q : F ⟶ h_V` be a morphism of
presheaves on that site. Read over the site of `V` itself, the source of `q` becomes the fibre
`CategoryTheory.OverShriek.fiber` of `q` over the tautological section, transported along the
iterated-slice equivalence. The every-étale-chart condition of Stacks 03MJ for `q` implies the
same condition for the structural morphism of that fibre.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_toYonedaId_iteratedSliceFiber`: a property of
  morphisms of schemes holds on every étale chart of the structural morphism of the slice fibre
  of `q` as soon as it holds on every étale chart of `q`.
* `CategoryTheory.OverShriek.relocalizeRestrictIteratedSliceIso`: restricting a presheaf on the
  slice over `T` to the smaller base `V.left` is reading it on the slice over `V`.

## Implementation notes

After the iterated-slice comparison, the fibre of `q` over the tautological section of `h_V` is
definitionally `CategoryTheory.OverShriek.fibreOfSection` of `q` over the identity of `h_V`
(`CategoryTheory.OverShriek.iteratedSliceBackward_comp_fiber_eq_fibreOfSection`).

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {X : C}

/-- **Restriction to a smaller base is reading a slice presheaf on a smaller slice.** For
`f : V ⟶ T` a morphism of the slice over `X`, restricting a presheaf on the slice over `T` along
`f.left` is precomposing with `CategoryTheory.Over.map f`, both read through the iterated-slice
equivalence. -/
def relocalizeRestrictIteratedSliceIso {V T : Over X} (f : V ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type v) :
    (relocalizeRestrict f.left).obj ((Over.iteratedSliceBackward T).op ⋙ F) ≅
      (Over.iteratedSliceBackward V).op ⋙ (Over.map f).op ⋙ F :=
  let e : Over.map f.left ⋙ Over.iteratedSliceBackward T ≅
      Over.iteratedSliceBackward V ⋙ Over.map f :=
    NatIso.ofComponents (fun A => Over.isoMk
      (Over.isoMk (Iso.refl A.left) (by
        change 𝟙 A.left ≫ (A.hom ≫ V.hom) = (A.hom ≫ f.left) ≫ T.hom
        simp [Category.assoc]))
      (by apply Over.OverMorphism.ext
          change 𝟙 A.left ≫ (A.hom ≫ f.left) = A.hom ≫ f.left
          simp)) (by
            intro A A' g
            apply Over.OverMorphism.ext
            apply Over.OverMorphism.ext
            change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
            simp)
  Functor.isoWhiskerRight (NatIso.op e.symm) F

/-- **The slice fibre of a morphism to a representable presheaf is a fibre over a section.** The
fibre of `q : F ⟶ h_V` over the tautological section of `h_V`, read on the slice over `V` through
the iterated-slice equivalence, is `CategoryTheory.OverShriek.fibreOfSection` of `q` over the
identity of `h_V`. -/
theorem iteratedSliceBackward_comp_fiber_eq_fibreOfSection (V : Over X)
    {F : (Over X)ᵒᵖ ⥤ Type v} (q : F ⟶ yoneda.obj V) :
    (Over.iteratedSliceBackward V).op ⋙ fiber (𝟙 (yoneda.obj V)) q =
      fibreOfSection V.hom q (𝟙 (yoneda.obj V)) :=
  rfl

end CategoryTheory.OverShriek

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structural morphism of the fibre of `q : F ⟶ h_V` over the tautological section is
`q`**, up to the isomorphism identifying the lower-shriek extension of that fibre with `F`. -/
theorem Space.relocalizeToYoneda_fibreOfSection_eq
    (V : BigFppfOver B S hS) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ yoneda.obj V) :
    ∃ e : (OverShriek.relocalizePresheafFunctor V.hom).obj
        (OverShriek.fibreOfSection V.hom q (𝟙 (yoneda.obj V))) ≅ F,
      OverShriek.relocalizeToYoneda V.hom
        (OverShriek.fibreOfSection V.hom q (𝟙 (yoneda.obj V))) = e.hom ≫ q := by
  have hpb := OverShriek.isPullback_relocalizeFibreOfSectionMap V.hom q (𝟙 (yoneda.obj V))
  exact ⟨hpb.isoIsPullback _ _ IsPullback.of_id_fst,
    (hpb.isoIsPullback_hom_snd _ _ IsPullback.of_id_fst).symm⟩

/-- **The every-étale-chart condition passes from a morphism to a representable presheaf to the
structural morphism of its slice fibre.** The fibre is read over the site of `V` itself, so its
structural morphism is the one to the representable presheaf of the terminal object of that
site. -/
theorem Space.holdsOnEveryEtaleChart_toYonedaId_iteratedSliceFiber
    (P : MorphismProperty Scheme.{u}) (V : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ yoneda.obj V)
    (hq : Space.HoldsOnEveryEtaleChart B S hS P q) :
    Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 P
      (Space.toYonedaId B V.left.1 V.left.2
        ((Over.iteratedSliceBackward V).op ⋙ OverShriek.fiber (𝟙 (yoneda.obj V)) q)) := by
  rw [OverShriek.iteratedSliceBackward_comp_fiber_eq_fibreOfSection]
  obtain ⟨e, he⟩ := Space.relocalizeToYoneda_fibreOfSection_eq B S hS V q
  exact (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V.left.1 S V.left.2 hS
    V.hom P _).1 (he ▸ (Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P e.hom q).2 hq)

end AlgebraicGeometry

end
