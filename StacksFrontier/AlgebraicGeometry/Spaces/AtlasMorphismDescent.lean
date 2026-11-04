module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Descending a morphism of presheaves along a surjective étale atlas

Let `F` be a presheaf on the big fppf site of a scheme `S` which is a sheaf and carries a
surjective étale atlas `b : yoneda.obj U ⟶ F`, and let `W` be a sheaf. A morphism
`k : yoneda.obj U ⟶ W` descends to `F` exactly when it is invariant under the kernel pair of `b`,
and the descended morphism is unique; in particular `b` can be cancelled on the left.

This file records those two statements with the kernel pair existentially quantified rather than
supplied, which is the form a descent argument uses, together with the companion separatedness
statement: a morphism out of a representable presheaf is determined by its restrictions along a
covering family.

## Main results

* `AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas`: an étale atlas has a represented
  kernel pair.
* `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`: a kernel-pair invariant morphism
  out of a surjective étale atlas descends uniquely.
* `AlgebraicGeometry.Space.hom_ext_of_etale_atlas`: a surjective étale atlas can be cancelled on
  the left.
* `AlgebraicGeometry.Space.hom_ext_of_cover`: a morphism out of a representable presheaf into a
  sheaf is determined by its restrictions along a covering family.
* `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_square`: a morphism between two étale
  atlases which is compatible with a kernel pair of each descends uniquely to the two
  quotients.

## Implementation notes

The kernel pair is represented because an étale morphism of presheaves is in particular
relatively representable, which is the first component of
`CategoryTheory.MorphismProperty.relative`; the two projections are the chosen pullback of the
atlas along itself, with the first one carried back along Yoneda, which is full.

The descent itself is `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`, i.e. the
fact that a surjective étale atlas is a coequalizer of its kernel pair in sheaves
(**Stacks 0262**, part (3)). Cancelling the atlas on the left is the uniqueness half of the same
statement applied to the common composite, so no separate local-surjectivity argument is needed.

Both statements ask only for the sheaf condition on `F` and `W`, not for algebraicity: the
representability of the atlas is already carried by the étaleness hypothesis.

A morphism of the two presentations `R' ⇉ U` and `R ⇉ V` descends by the same token, which is
the last step of the proof of Stacks 04KL: there the two presentations are `U ×_X U ⇉ U` of `X`
and `V ×_Y V ⇉ V` of `Y`, and the compatibility of the morphism of charts with the two kernel
pairs is what makes the two composites `U ×_X U ⟶ V ⟶ Y` agree. Only the source presentation
needs to be an atlas; of the target one only a kernel pair is used, so no hypothesis on the
target chart is required beyond the sheaf condition on `Y`.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale atlas of a presheaf has a represented kernel pair.** An étale morphism of
presheaves is relatively representable, so the fibre product of the atlas with itself is
represented by an object of the site. -/
theorem exists_kernelPair_of_etale_atlas {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (b : yoneda.obj U ⟶ F)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) b b := by
  refine ⟨hetale.rep.pullback b, yoneda.preimage (hetale.rep.fst b), hetale.rep.snd b, ?_⟩
  rw [yoneda.map_preimage]
  exact hetale.rep.isPullback b

/-- **A morphism out of a surjective étale atlas which is invariant under every represented
kernel pair of the atlas descends uniquely.** The atlas is a coequalizer of its kernel pair in
sheaves (**Stacks 0262**, part (3)), so invariance is exactly the condition for a factorization,
and the factorization is unique. -/
theorem existsUnique_hom_of_atlas_invariant {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {U : BigFppfOver B S hS} (b : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (k : yoneda.obj U ⟶ W)
    (hcompat : ∀ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) b b →
        yoneda.map s ≫ k = yoneda.map t ≫ k) :
    ∃! d : F ⟶ W, b ≫ d = k := by
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B S hS b hetale
  exact existsUnique_desc_of_surjective_etale_atlas B S hS hF b hR hsurj hetale hW k
    (hcompat R s t hR)

/-- **A surjective étale atlas of a presheaf can be cancelled on the left.** Two morphisms into a
sheaf agreeing after the atlas both factor the common composite through it, and that
factorization is unique by
`AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`. -/
theorem hom_ext_of_etale_atlas {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    {U : BigFppfOver B S hS} (b : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    {f g : F ⟶ W} (hfg : b ≫ f = b ≫ g) : f = g := by
  obtain ⟨d, -, hu⟩ := existsUnique_hom_of_atlas_invariant B S hS hF hW b hsurj hetale (b ≫ f)
    fun _ s t hR => by simp only [← Category.assoc, hR.w]
  rw [hu f rfl, hu g hfg.symm]

/-- **A morphism out of a representable presheaf into a sheaf is determined by its restrictions
along a covering family.** This is separatedness of the target for the covering presieve. -/
theorem hom_ext_of_cover {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (T : BigFppfOver B S hS) {I : Type u} (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T)
    (hcover : Sieve.generate (Presieve.ofArrows V π) ∈ BigFppfOver.topology B S hS T)
    {f g : yoneda.obj T ⟶ W} (hfg : ∀ i, yoneda.map (π i) ≫ f = yoneda.map (π i) ≫ g) :
    f = g := by
  have hsf : Presieve.IsSheafFor W (Presieve.ofArrows V π) :=
    (Presieve.isSheafFor_iff_generate (P := W) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp hW) _ hcover)
  refine yonedaEquiv.injective (hsf.isSeparatedFor.ext fun R r hr => ?_)
  obtain ⟨i⟩ := hr
  simpa [yonedaEquiv_naturality] using congrArg yonedaEquiv (hfg i)

/-- **A morphism of presentations descends to the quotients** (the gluing step of the source's
proof of Stacks 04KL, which is stated in full as
`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged`). Let `p : h_U ⟶ X` be
a surjective étale atlas of a sheaf `X` with kernel pair `s', t' : R' ⟶ U`, let `q : h_V ⟶ Y` be
a morphism to a sheaf `Y` with kernel pair `sV, tV : R ⟶ V`, and let `a : U ⟶ V` and
`c : R' ⟶ R` be a morphism of the two resulting diagrams of schemes. Then there is a unique
morphism `f : X ⟶ Y` whose restriction to the atlas is `a` followed by `q`. -/
theorem existsUnique_hom_of_atlas_square {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {U R' V R : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    {s' t' : R' ⟶ U} (hR' : IsPullback (yoneda.map s') (yoneda.map t') p p)
    {sV tV : R ⟶ V} (hR : IsPullback (yoneda.map sV) (yoneda.map tV) q q)
    (a : U ⟶ V) (c : R' ⟶ R) (hs : s' ≫ a = c ≫ sV) (ht : t' ≫ a = c ≫ tV) :
    ∃! f : X ⟶ Y, p ≫ f = yoneda.map a ≫ q := by
  refine existsUnique_desc_of_surjective_etale_atlas B S hS hX p hR' hsurj hetale hY
    (yoneda.map a ≫ q) ?_
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hs, ht, Functor.map_comp_assoc,
    Functor.map_comp_assoc, hR.w]

end AlgebraicGeometry.Space

end
