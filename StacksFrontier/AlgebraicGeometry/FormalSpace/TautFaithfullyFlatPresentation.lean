module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSurjectiveFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatQuotientOpenIdeal

/-!
# The taut homomorphism with faithfully flat quotients of a surjective flat morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces, surjective
and flat, with `X` countably indexed and presented by the weakly admissible topological ring
`C`. Then `Y` is McQuillan, it has a presenting ring `A`, and under the resulting
identifications `X = Spf C` and `Y = Spf A` the morphism `f` is the formal spectrum of a
continuous homomorphism `φ : A → C` which is taut and all of whose maps on quotients by open
ideals are faithfully flat.

This is the passage from geometry to algebra that the proofs of **Stacks 0GXR**, **Stacks
0GXS**, **Stacks 0AKT** and **Stacks 0AKW** make before applying the ring-theoretic descent
lemmas of Stacks 0GXM, 0GXP and 0GXQ.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`:
  the homomorphism `φ`, together with the presenting ring `A` of the target.

## Implementation notes

The hypothesis that `X` be countably indexed is what the source assumes too, and it cannot be
dropped: it is the only route to the target being McQuillan at all. The source's argument is the
forward implication of **Stacks 0AKS**
(`AlgebraicGeometry.FormalSpace.isCountablyIndexed_target_of_surjective_flat`), which makes `Y`
countably indexed and hence McQuillan with a presenting ring by item (6) of **Stacks 0AIK**
(`AlgebraicGeometry.FormalSpace.isPresentingRing_of_isCountablyIndexed`). Each of the four
lemmas listed above has it: for Stacks 0GXR it is half of the hypothesis, and for the other
three it is items (1), (2), (3) and (5) of Stacks 0AIK applied to the type of `X`.

Given the two presenting rings, `φ` is **Stacks 0AN0** — full faithfulness of `Spf`, in the form
of `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq` — applied to
`f` read through the two identifications
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation.formalSpectrumIso`. Tautness is the
implication (1) ⟹ (3) of **Stacks 0AN5**, which is
`FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine`;
representability by algebraic spaces transports from `f` to `Spf φ` along the two identifications.

Faithful flatness of the quotient maps is produced first at the weak ideals of definition of
`A`. There the quotient `Spec (A ⧸ I)` is a stage of the presentation of `Y`, and the base
change of `f` along its inclusion is the corresponding stage `Spec (C ⧸ (I C)‾)` of the
presentation of `X` — the computation `C ⊗̂_A A ⧸ I = C ⧸ (I C)‾` of **Stacks 0AMZ**, carried by
`AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`. Surjectivity and
flatness of `f` make that base change faithfully flat on coordinate rings, which is
`AlgebraicGeometry.FormalSpace.faithfullyFlat_of_isPullback_of_surjective_flat`, and the
coordinate ring map is `Spec` of the quotient map. An arbitrary open ideal `I` of `A` contains a
weak ideal of definition — intersect one with `I` — and faithful flatness rises from it to `I`
by `RingHom.faithfullyFlat_quotientMap_closure_of_le`, because the quotient map at `I` is a base
change of the one at the smaller ideal.

## References

* [Stacks Project, Tag 00HQ](https://stacks.math.columbia.edu/tag/00HQ)
* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

/-! ### Two transport steps -/

/-- Representability by algebraic spaces transports along isomorphisms of the source and the
target: a base change of `eF.hom ≫ a ≫ eG.hom` along a scheme-valued point `ξ` is a base change
of `a` along `ξ ≫ eG.inv`. -/
private theorem isRepresentableByAlgebraicSpacesULift_comp_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a)
    (eF : F' ≅ F) (eG : G ≅ G') :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (eF.hom ≫ a ≫ eG.hom) := by
  intro U ξ
  have hsq : IsPullback (pullback.fst (ξ ≫ eG.inv) a)
      (pullback.snd (ξ ≫ eG.inv) a ≫ eF.inv) ξ (eF.hom ≫ a ≫ eG.hom) :=
    (IsPullback.of_hasPullback (ξ ≫ eG.inv) a).of_iso (Iso.refl _) (Iso.refl _) eF.symm eG
      (by simp) (by simp) (by simp) (by simp)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback (ha U (ξ ≫ eG.inv))

/-- Representability by algebraic spaces transports along isomorphisms of the source and the
target of a morphism of fppf sheaves. -/
private theorem isRepresentableByAlgebraicSpacesULift_sheaf_comp_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (eX : X' ≅ X) (eY : Y ≅ Y') :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (eX.hom ≫ f ≫ eY.hom).hom :=
  isRepresentableByAlgebraicSpacesULift_comp_iso B S hS f.hom hf
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso eX)
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso eY)

/-- Faithful flatness of a homomorphism of commutative rings is read off the morphism of
coordinate rings of its spectrum, the two being conjugate by the unit of the
global-sections–spectrum adjunction. -/
private theorem faithfullyFlat_of_faithfullyFlat_appTop_specMap {R T : CommRingCat.{u}}
    (ψ : R ⟶ T) (h : (((Spec.map ψ).appTop).hom).FaithfullyFlat) : (ψ.hom).FaithfullyFlat := by
  have he : ψ.hom = ((Scheme.ΓSpecIso T).hom.hom).comp
      ((((Spec.map ψ).appTop).hom).comp ((Scheme.ΓSpecIso R).inv.hom)) := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    simp
  rw [he]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)) h)
    (RingHom.FaithfullyFlat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso T).hom))

/-! ### The passage from geometry to algebra -/

/-- **The taut homomorphism with faithfully flat quotients attached to a surjective flat
morphism of affine formal algebraic spaces.** Let `f : X ⟶ Y` be a morphism of affine formal
algebraic spaces over `S` which is representable by algebraic spaces, surjective and flat, with
`X` countably indexed and presented by the weakly admissible topological ring `C`. Then `Y` is
McQuillan and has a presenting ring `A`, and there is a continuous taut homomorphism
`φ : A → C` all of whose maps on quotients by open ideals are faithfully flat.

This is the passage from geometry to algebra in the proofs of Stacks 0GXR, 0GXS, 0AKT and
0AKW. Countable indexing of the target is the forward implication of Stacks 0AKS, so the target
is McQuillan by item (6) of Stacks 0AIK; `φ` is Stacks 0AN0 and is taut by the implication
(1) ⟹ (3) of Stacks 0AN5. Faithful flatness of the quotient maps comes from the stage base
change of Stacks 0AMZ together with surjectivity and flatness, first at the weak ideals of
definition of `A` and then at every open ideal.

NO TAG IS ATTACHED: every ingredient is registered where it is proved, and the Stacks project
states no lemma with this content. -/
theorem exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) a.hom) f.hom hrep)
    (hXc : IsCountablyIndexed B S hS X)
    (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
    (_ : IsLinearTopology C C) (hC : IsPresentingRing B S hS C X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (φ : A →+* C),
      HasSomeSurjectivePresentation B S hS Y ∧ IsPresentingRing B S hS A Y ∧
        Continuous φ ∧ RingHom.IsTaut φ ∧
        ∀ I : Ideal A, IsOpen (I : Set A) →
          (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
            (Ideal.map_le_iff_le_comap.mp (fun _ hx ↦ subset_closure hx))).FaithfullyFlat := by
  classical
  have hYc : IsCountablyIndexed B S hS Y :=
    isCountablyIndexed_target_of_surjective_flat B S hS f hX hY hrep hsurj hflat hXc
  obtain ⟨hYmcq, A, hAR, hAT, hATR, hALT, hApres⟩ :=
    isPresentingRing_of_isCountablyIndexed B S hS hY hYc
  obtain ⟨PX⟩ := hC.2
  obtain ⟨PY⟩ := hApres.2
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hApres.1 hC.1
    (PX.formalSpectrumIso.inv ≫ f ≫ PY.formalSpectrumIso.hom)
  -- tautness, from the implication (1) ⟹ (3) of Stacks 0AN5
  have hrepSpf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hApres.1 g).hom := by
    rw [hg]
    exact isRepresentableByAlgebraicSpacesULift_sheaf_comp_iso B S hS f hrep
      PX.formalSpectrumIso.symm PY.formalSpectrumIso
  have htaut : RingHom.IsTaut g.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS
      hApres.1 hC.1 PY.quotientSystem PX.quotientSystem
      (isAffineFormalAlgebraicSpace_of_iso B S hS PY.formalSpectrumIso hY)
      (isAffineFormalAlgebraicSpace_of_iso B S hS PX.formalSpectrumIso hX) g hrepSpf
  -- faithful flatness of the quotient maps at the weak ideals of definition of `A`
  have hwid : ∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      (Ideal.quotientMap (Ideal.closure (I.map g.toRingHom)) g.toRingHom
        (Ideal.map_le_iff_le_comap.mp fun _ hx ↦ subset_closure hx)).FaithfullyFlat := by
    intro I hI
    obtain ⟨⟨K, hKwid⟩, hKeq, hIK, sq⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS
      hApres.1 hC.1 PY.quotientSystem PX.quotientSystem g htaut ⟨I, hI⟩
    subst hKeq
    have sq' : IsPullback
        (formalSpectrumInclusion PX.quotientSystem ⟨_, hKwid⟩ ≫ PX.formalSpectrumIso.inv)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (g.stageMap ⟨I, hI⟩ ⟨_, hKwid⟩ hIK)))
        f (formalSpectrumInclusion PY.quotientSystem ⟨I, hI⟩ ≫ PY.formalSpectrumIso.inv) := by
      refine sq.of_iso (Iso.refl _) PX.formalSpectrumIso.symm (Iso.refl _)
        PY.formalSpectrumIso.symm (Category.id_comp _).symm ?_ ?_ (Category.id_comp _).symm
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · change formalSpectrumMap hApres.1 g ≫ PY.formalSpectrumIso.inv
            = PX.formalSpectrumIso.inv ≫ f
        rw [hg, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hff := faithfullyFlat_of_isPullback_of_surjective_flat B S hS f hrep hsurj hflat
      (BigAffineFppf.isAffine_toScheme_obj B S hS (PY.quotientSystem.stage ⟨I, hI⟩))
      (BigAffineFppf.isAffine_toScheme_obj B S hS (PX.quotientSystem.stage ⟨_, hKwid⟩)) sq'
    exact faithfullyFlat_of_faithfullyFlat_appTop_specMap _ hff
  refine ⟨A, hAR, hAT, hATR, hALT, g.toRingHom, hYmcq, hApres, g.continuous, htaut, ?_⟩
  intro I hIopen
  obtain ⟨W, hW⟩ := hApres.1.1
  have hWI : TopologicalRing.IsWeakIdealOfDefinition (W ⊓ I) :=
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hW hIopen
  exact RingHom.faithfullyFlat_quotientMap_closure_of_le g.toRingHom inf_le_right
    (htaut.1 (W ⊓ I) hWI.1) (hwid (W ⊓ I) hWI)

end AlgebraicGeometry.FormalSpace

end
