module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleLocalOnSource
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
public import StacksFrontier.CategoryTheory.Sites.SheafFibreProductObj

/-!
# A morphism out of a coproduct of sheaves is étale when each restriction is

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a coproduct of a family `Q` of
fppf sheaves with values in `Type (max w u)`, and let `c : P ⟶ R` be a morphism of presheaves
out of it. This file proves that `c` is étale in the sense of **Stacks 03FR**, that is
`AlgebraicGeometry.Space.IsEtaleULift`, as soon as each restriction `ι i ≫ c` is.

This is the étale half of the step from condition (2) to condition (3) of **Stacks 0AJ9**: there
the coproduct is the coproduct of the finitely many members of an atlas as in Definition 0AIM,
and the restrictions are the members' own structure morphisms.

## Main results

* `AlgebraicGeometry.Space.isEtaleULift_of_isColimit_cofan`: **a morphism out of a coproduct of
  pointwise `u`-small fppf sheaves is étale as soon as its restriction to every summand is.**
* `AlgebraicGeometry.Space.isEtaleULift_iso_hom_comp_iff`: étaleness is invariant under an
  isomorphism of the source.
* `AlgebraicGeometry.Space.isRepresentableEtale_of_isColimit_cofan`: **a morphism out of a
  coproduct of fppf sheaves is representable by algebraic spaces and étale as soon as each of
  its restrictions is**, which is the étale half of the step from condition (2) to condition (3)
  of Stacks 0AJ9 together with its representability companion.

## Implementation notes

`AlgebraicGeometry.Space.IsEtaleULift` quantifies over the étale scheme-valued points of the
*source*, so what has to be shown is that the composite of `c` with an étale morphism
`φ : U ⟶ P` out of a universe-lifted representable is étale. The three inputs are:

* the clopen decomposition of `U` along the coproduct, Stacks 02WO in this value universe
  (`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan_ulift`), which splits
  `U` into open pieces on each of which `φ` factors through one member;
* that the legs of the coproduct are monomorphisms in this value universe
  (`AlgebraicGeometry.Sheaf.mono_hom_cofan_inj_bigFppfOver_ulift`), which is what makes that
  factorisation itself étale, by
  `CategoryTheory.MorphismProperty.relative_of_comp_mono`;
* that étaleness of a morphism out of a universe-lifted representable is local on the source
  (`AlgebraicGeometry.Space.relative_etaleOnSite_of_openCover_source`), which assembles the
  pieces.

Representability of `φ ≫ c` is a hypothesis, as it is in the locality statement: the
representing objects of the base changes over the pieces would have to be glued along an open
covering to produce it, and that glueing is not available. Where this is applied the target `R`
is itself a universe-lifted representable, so the hypothesis is discharged by full faithfulness
of `CategoryTheory.uliftYoneda`.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism out of a coproduct of pointwise `u`-small fppf sheaves is étale as soon as its
restriction to every summand is**, for a value universe independent of the universe of the
schemes.

A scheme-valued point `φ : U ⟶ P` of the source which is étale decomposes `U` into open pieces,
one for each member of the family, on which `φ` factors through that member; the factorisation
is étale because the leg of the coproduct is a monomorphism, so the restriction of `φ ≫ c` to
the piece is étale by the hypothesis on that member, and étaleness is local on the source. -/
theorem isEtaleULift_of_isColimit_cofan {I : Type v} [Small.{u} I]
    {Q : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hQ : ∀ i, FunctorToTypes.Small.{u} (Q i).obj)
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Q i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι))
    {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (c : P.obj ⟶ R)
    (hrep : ∀ (V : BigFppfOver B S hS) (φ : (uliftYoneda.{w}).obj V ⟶ P.obj),
      (uliftYoneda.{w}).relativelyRepresentable (φ ≫ c))
    (hetale : ∀ i, IsEtaleULift.{w} B S hS ((ι i).hom ≫ c)) :
    IsEtaleULift.{w} B S hS c := by
  have _ : (etaleOnSite B S hS).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  intro V φ hφ
  obtain ⟨W', p, hoi, hsec, -, hcov, -⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan_ulift B S hS hQ ι hP V
      (uliftYonedaEquiv.{w} φ)
  refine relative_etaleOnSite_of_openCover_source B S hS (hrep V φ) p hoi hcov fun i => ?_
  obtain ⟨z, hz⟩ := hsec i
  -- the factorisation of the restriction of `φ` through the `i`-th member
  have hfac : uliftYonedaEquiv.{w}.symm z ≫ (ι i).hom = (uliftYoneda.{w}).map (p i) ≫ φ := by
    refine uliftYonedaEquiv.{w}.injective ?_
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, hz,
      uliftYonedaEquiv_naturality φ (p i).op]
    rfl
  -- the restriction of `φ` to the `i`-th piece is étale, `p i` being an open immersion
  have hpi : (etaleOnSite B S hS).relative (uliftYoneda.{w})
      ((uliftYoneda.{w}).map (p i)) := by
    rw [relative_etale_uliftYoneda_map_iff]
    have _ := hoi i
    infer_instance
  have _ : Mono (ι i).hom := Sheaf.mono_hom_cofan_inj_bigFppfOver_ulift B S hS hQ ι hP i
  have hψ : (etaleOnSite B S hS).relative (uliftYoneda.{w}) (uliftYonedaEquiv.{w}.symm z) :=
    MorphismProperty.relative_of_comp_mono (uliftYoneda.{w}) _ _ (ι i).hom
      (hfac ▸ relative_comp B S hS hpi hφ)
  have hres := hetale i (W' i) (uliftYonedaEquiv.{w}.symm z) hψ
  rwa [← Category.assoc, hfac, Category.assoc] at hres

/-! ### Invariance under an isomorphism of the source -/

/-- **Étaleness of a morphism of presheaves is invariant under an isomorphism of its source.**
`AlgebraicGeometry.Space.IsEtaleULift` quantifies over the étale scheme-valued points of the
source, and those correspond across an isomorphism, relative étaleness being invariant under
postcomposition with an isomorphism. -/
theorem isEtaleULift_iso_hom_comp_iff
    {F' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F' ≅ F) (c : F ⟶ G) :
    IsEtaleULift.{w} B S hS (e.hom ≫ c) ↔ IsEtaleULift.{w} B S hS c := by
  constructor
  · intro h V φ hφ
    rw [show φ ≫ c = (φ ≫ e.inv) ≫ e.hom ≫ c by simp]
    exact h V (φ ≫ e.inv) (MorphismProperty.RespectsIso.postcomp _ e.inv _ hφ)
  · intro h V φ hφ
    rw [← Category.assoc]
    exact h V (φ ≫ e.hom) (MorphismProperty.RespectsIso.postcomp _ e.hom _ hφ)

/-! ### A morphism out of a coproduct, representable by algebraic spaces and étale -/

/-- **A morphism of fppf sheaves out of a coproduct is representable by algebraic spaces and
étale as soon as each of its restrictions to a summand is**, for a value universe independent of
the universe of the schemes and a `u`-small index type.

The base change of the morphism along a scheme-valued point of its target decomposes as the
coproduct of the base changes of the restrictions
(`CategoryTheory.Sheaf.exists_isColimit_cofan_pullback_of_comp`). Each of those is an algebraic
space and étale over the point by hypothesis, so the base change is an algebraic space by
Stacks 02WQ in this value universe and is étale over the point by
`AlgebraicGeometry.Space.isEtaleULift_of_isColimit_cofan`.

The hypothesis `hV` is the one Stacks 02WQ cannot do without: the chosen atlases of the base
changes have to have a coproduct *inside* the site. For a finite index type it is
`AlgebraicGeometry.hasFiniteCoproducts_bigFppfOver`.

Sheafification in the value universe is an instance argument because the coproduct of sheaves
whose base change is decomposed is formed by it; at the value universe of a formal algebraic
space it is available. -/
theorem isRepresentableEtale_of_isColimit_cofan {I : Type v} [Small.{u} I]
    {Z : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Z i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι))
    {W : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (a : P ⟶ W)
    [HasSheafify (BigFppfOver.topology B S hS) (Type (max w u))]
    (hV : ∀ U : I → BigFppfOver B S hS, ∃ (V : BigFppfOver B S hS) (j : ∀ i, U i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V j)))
    (hg : ∀ i, ∃ h : IsRepresentableByAlgebraicSpacesULift.{w} B S hS (ι i ≫ a).hom,
      HasPropertyULift.{w} B S hS
        (fun _ _ k ↦ IsEtaleULift.{w} B S hS k.hom) (ι i ≫ a).hom h) :
    ∃ h : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a.hom,
      HasPropertyULift.{w} B S hS (fun _ _ k ↦ IsEtaleULift.{w} B S hS k.hom) a.hom h := by
  classical
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : Small.{max w u} I :=
    ⟨⟨ULift.{w} (Shrink.{u} I), ⟨(equivShrink.{u} I).trans Equiv.ulift.symm⟩⟩⟩
  have hsheaf : ∀ U : BigFppfOver B S hS, Presheaf.IsSheaf J ((uliftYoneda.{w}).obj U) :=
    fun U => (isSheaf_iff_isSheaf_of_type _ _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  choose hrepi hetalei using hg
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ W.obj),
      IsAlgebraicSpaceULift.{w} B S hS (pullback ξ a.hom) ∧
        IsEtaleULift.{w} B S hS (pullback.fst ξ a.hom) := by
    intro U ξ
    let Ush : Sheaf J (Type (max w u)) := ⟨(uliftYoneda.{w}).obj U, hsheaf U⟩
    let t : Ush ⟶ W := ObjectProperty.homMk ξ
    obtain ⟨l, hlfst, -, ⟨hcofan⟩⟩ :=
      Sheaf.exists_isColimit_cofan_pullback_of_comp J ι hP a t
    -- each summand of the base change is an algebraic space, and étale over the point
    have halg : ∀ i, IsAlgebraicSpaceULift.{w} B S hS (pullback t (ι i ≫ a)).obj := fun i =>
      isAlgebraicSpaceULift_of_iso B S hS (Sheaf.pullbackObjIso t (ι i ≫ a)).symm
        (hrepi i U ξ)
    have hpiece : ∀ i, IsEtaleULift.{w} B S hS (pullback.fst t (ι i ≫ a)).hom := by
      intro i
      rw [← Sheaf.pullbackObjIso_hom_fst t (ι i ≫ a)]
      exact (isEtaleULift_iso_hom_comp_iff B S hS _ _).mpr (hetalei i U ξ)
    -- the base change is an algebraic space, by Stacks 02WQ in this value universe
    choose Uat fat hfsurj hfetale using fun i => (halg i).exists_atlas
    obtain ⟨V, j, ⟨hVcol⟩⟩ := hV Uat
    have halgtot : IsAlgebraicSpaceULift.{w} B S hS (pullback t a).obj :=
      isAlgebraicSpaceULift_coproduct B S hS halg l hcofan Uat fat hfsurj hfetale hVcol
    -- and it is étale over the point, by the étale half
    have hetaletot : IsEtaleULift.{w} B S hS (pullback.fst t a).hom := by
      refine isEtaleULift_of_isColimit_cofan B S hS
        (fun i => small_of_isAlgebraicSpaceULift B S hS (halg i)) l hcofan _ ?_ ?_
      · intro V' φ
        simpa using Functor.relativelyRepresentable.map (uliftYoneda.{w})
          ((uliftYoneda.{w}).preimage (φ ≫ (pullback.fst t a).hom))
      · intro i
        rw [show (l i).hom ≫ (pullback.fst t a).hom = (pullback.fst t (ι i ≫ a)).hom from
          congrArg (fun k : pullback t (ι i ≫ a) ⟶ Ush => k.hom) (hlfst i)]
        exact hpiece i
    refine ⟨isAlgebraicSpaceULift_of_iso B S hS (Sheaf.pullbackObjIso t a) halgtot, ?_⟩
    rw [← Sheaf.pullbackObjIso_hom_fst t a] at hetaletot
    exact (isEtaleULift_iso_hom_comp_iff B S hS _ _).mp hetaletot
  exact ⟨fun U ξ => (key U ξ).1, fun U ξ => (key U ξ).2⟩

end AlgebraicGeometry.Space

end
