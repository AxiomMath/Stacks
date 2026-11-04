module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingTransfer
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SingleDegreeRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Restriction along an open immersion and restriction to its image

Let `j : U ⟶ X` be an open immersion of schemes. The `Ext`-groups of the core case of
[Stacks, Tag 0G2H] are available for the restriction functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` of an *open subscheme* `V : X.Opens`
(`Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict` and the degree-zero
bijectivity proved with it), whereas the dévissage of the tag runs on
`AlgebraicGeometry.Scheme.Modules.restrictFunctor j` for the open immersion `j` itself. This file
identifies the two over the image of `j`.

The identification is the factorization `j = (isomorphism onto the image) ≫ (inclusion of the
image)` of `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`, read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`: restriction along `j` is restriction to
the open subscheme `j.opensRange` followed by restriction along an *isomorphism of schemes*. The
latter is an equivalence of categories of modules
(`AlgebraicGeometry.Scheme.Modules.isEquivalence_restrictFunctor_of_isIso`), hence induces an
equivalence of derived categories
(`Stacks.Injectives.mapDerivedCategory_isEquivalence`), and in particular a fully faithful
functor — which is all that `CategoryTheory.RestrictionLifting` is sensitive to.

So the statement of [Stacks, Tag 0G2H] for `restrictFunctor j.opensRange.ι` is the statement for
`restrictFunctor j`: that is
`AlgebraicGeometry.restrictionLifting_mapDerivedCategory_of_opensRange`, and
`AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange` is the composite with
`CategoryTheory.restrictionLifting_singleFunctor_of_ext`, which is the form the `i = 0`
`Ext`-colimit statement is consumed in.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isEquivalence_restrictFunctor_of_isIso`: restriction along an
  isomorphism of schemes is an equivalence of categories of modules.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoOpensRange`: **the identification** —
  restriction along `j` is restriction to the image of `j` followed by restriction along the
  isomorphism of `U` with that image.
* `AlgebraicGeometry.Scheme.Modules.mapDerivedCategoryRestrictIsoOpensRange`: the same on derived
  categories.
* `CategoryTheory.RestrictionLifting.of_natIsoFunctor` and
  `CategoryTheory.RestrictionLifting.comp_fullyFaithful`: the two transfers of
  `CategoryTheory.RestrictionLifting` in the restricting functor.
* `AlgebraicGeometry.restrictionLifting_mapDerivedCategory_of_opensRange` and
  `AlgebraicGeometry.restrictionLifting_singleFunctor_of_ext_opensRange`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open InverseSequence

universe w v u u' u''

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- **`CategoryTheory.RestrictionLifting` only depends on the restricting functor up to
isomorphism.** Both halves are the hypothesis conjugated by the components of the isomorphism. -/
public lemma RestrictionLifting.of_natIsoFunctor {F : ℕᵒᵖ ⥤ 𝒟} {R R' : 𝒟 ⥤ 𝒞} (N : 𝒟)
    (e : R ≅ R') (h : RestrictionLifting F R N) : RestrictionLifting F R' N := by
  have key : ∀ {A B : 𝒟} (f : A ⟶ B),
      R'.map f = e.inv.app A ≫ R.map f ≫ e.hom.app B := fun f => by
    rw [e.hom.naturality f, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  constructor
  · intro n g
    obtain ⟨m, hm, f, hf⟩ := h.lift n (e.hom.app (F.obj (op n)) ≫ g ≫ e.inv.app N)
    refine ⟨m, hm, f, ?_⟩
    rw [key, hf, key (tr F hm)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  · intro n f g hfg
    refine h.eq n f g ?_
    rw [key f, key g] at hfg
    exact (cancel_mono (e.hom.app N)).mp ((cancel_epi (e.inv.app (F.obj (op n)))).mp hfg)

/-- **`CategoryTheory.RestrictionLifting` is stable under postcomposition with a fully faithful
functor.** A morphism out of `E R F_n` is `E` of a morphism out of `R F_n` by fullness, and two
morphisms agreeing after `E` agree by faithfulness. -/
public lemma RestrictionLifting.comp_fullyFaithful {𝒞' : Type u''} [Category.{v} 𝒞']
    {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (N : 𝒟) (E : 𝒞 ⥤ 𝒞') [E.Full] [E.Faithful]
    (h : RestrictionLifting F R N) : RestrictionLifting F (R ⋙ E) N := by
  constructor
  · intro n g
    obtain ⟨g₀, rfl⟩ := E.map_surjective g
    obtain ⟨m, hm, f, hf⟩ := h.lift n g₀
    exact ⟨m, hm, f, (congrArg E.map hf).trans (E.map_comp _ _)⟩
  · exact fun n f g hfg => h.eq n f g (E.map_injective hfg)

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/-- **Restriction along an isomorphism of schemes is an equivalence of categories of modules.**
Restriction along the inverse isomorphism is a quasi-inverse: the two composites are restriction
along the two composites of the isomorphism, which are identities, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorId`. -/
public lemma isEquivalence_restrictFunctor_of_isIso (f : U ⟶ X) [IsIso f] :
    (restrictFunctor f).IsEquivalence :=
  Functor.IsEquivalence.mk' (restrictFunctor (inv f))
    (restrictFunctorId.symm ≪≫
      restrictFunctorCongr (show 𝟙 X = inv f ≫ f from (IsIso.inv_hom_id f).symm) ≪≫
      restrictFunctorComp (inv f) f)
    ((restrictFunctorComp f (inv f)).symm ≪≫
      restrictFunctorCongr (IsIso.hom_inv_id f) ≪≫ restrictFunctorId)

/-- **The identification of restriction along an open immersion with restriction to its image.**
For an open immersion `j : U ⟶ X`, restriction along `j` is restriction to the open subscheme
`j.opensRange` followed by restriction along the isomorphism `U ≅ j.opensRange`.

This is `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` applied to the factorization
`j = j.isoOpensRange.hom ≫ j.opensRange.ι`. -/
public def restrictFunctorIsoOpensRange (j : U ⟶ X) [IsOpenImmersion j] :
    restrictFunctor j ≅
      restrictFunctor j.opensRange.ι ⋙ restrictFunctor j.isoOpensRange.hom :=
  restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι j).symm ≪≫
    restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The identification of restriction along an open immersion with restriction to its image, on
derived categories.** It is `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoOpensRange` read
through `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`. -/
public def mapDerivedCategoryRestrictIsoOpensRange (j : U ⟶ X) [IsOpenImmersion j] :
    (restrictFunctor j).mapDerivedCategory ≅
      (restrictFunctor j.opensRange.ι).mapDerivedCategory ⋙
        (restrictFunctor j.isoOpensRange.hom).mapDerivedCategory :=
  letI : PreservesFiniteLimits (restrictFunctor j.opensRange.ι ⋙
      restrictFunctor j.isoOpensRange.hom) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (restrictFunctor j.opensRange.ι ⋙
      restrictFunctor j.isoOpensRange.hom) := comp_preservesFiniteColimits _ _
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (restrictFunctorIsoOpensRange j) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **Restriction along an isomorphism of schemes induces an equivalence of derived categories of
modules.** -/
public lemma isEquivalence_mapDerivedCategory_restrictFunctor_of_isIso (f : U ⟶ X) [IsIso f] :
    (restrictFunctor f).mapDerivedCategory.IsEquivalence :=
  have := isEquivalence_restrictFunctor_of_isIso f
  Stacks.Injectives.mapDerivedCategory_isEquivalence (restrictFunctor f)

end Derived

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {U X : Scheme.{u}}

/-- **[Stacks, Tag 0G2H] for restriction to the image of `j` gives it for restriction along
`j`.** The two restriction functors differ by postcomposition with the equivalence of derived
categories induced by the isomorphism of `U` with the image of `j`
(`AlgebraicGeometry.Scheme.Modules.mapDerivedCategoryRestrictIsoOpensRange`), and
`CategoryTheory.RestrictionLifting` is insensitive to postcomposition with a fully faithful
functor and to an isomorphism of the restricting functor. -/
public lemma restrictionLifting_mapDerivedCategory_of_opensRange (j : U ⟶ X)
    [IsOpenImmersion j] (F : ℕᵒᵖ ⥤ DerivedCategory X.Modules) (N : DerivedCategory X.Modules)
    (h : RestrictionLifting F
      (Scheme.Modules.restrictFunctor j.opensRange.ι).mapDerivedCategory N) :
    RestrictionLifting F (Scheme.Modules.restrictFunctor j).mapDerivedCategory N :=
  have := Scheme.Modules.isEquivalence_mapDerivedCategory_restrictFunctor_of_isIso
    j.isoOpensRange.hom
  RestrictionLifting.of_natIsoFunctor N
    (Scheme.Modules.mapDerivedCategoryRestrictIsoOpensRange j).symm
    (h.comp_fullyFaithful N
      (Scheme.Modules.restrictFunctor j.isoOpensRange.hom).mapDerivedCategory)

/-- **The core case of [Stacks, Tag 0G2H] for restriction along an open immersion, from the
`Ext`-colimit statement over the image.** This is
`CategoryTheory.restrictionLifting_singleFunctor_of_ext` for the restriction functor of the open
subscheme `j.opensRange`, transported to `j` by
`AlgebraicGeometry.restrictionLifting_mapDerivedCategory_of_opensRange`. Its two hypotheses are
exactly the shape in which the degree-zero case
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero`
are stated, those being about `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` for
`V : X.Opens`. -/
public lemma restrictionLifting_singleFunctor_of_ext_opensRange (j : U ⟶ X) [IsOpenImmersion j]
    [HasExt.{w} X.Modules] [HasExt.{w} j.opensRange.toScheme.Modules]
    (S : ℕᵒᵖ ⥤ X.Modules) (B : X.Modules) (p q : ℤ) (i : ℕ) (hi : q + (i : ℤ) = p)
    (hlift : ∀ (n : ℕ) (η : Ext.{w}
      ((Scheme.Modules.restrictFunctor j.opensRange.ι).obj (S.obj (op n)))
      ((Scheme.Modules.restrictFunctor j.opensRange.ι).obj B) i),
      ∃ (m : ℕ) (h : n ≤ m) (ξ : Ext.{w} (S.obj (op m)) B i),
        ξ.mapExactFunctor (Scheme.Modules.restrictFunctor j.opensRange.ι) =
          (Ext.mk₀ ((Scheme.Modules.restrictFunctor j.opensRange.ι).map (tr S h))).comp η
            (zero_add i))
    (heq : ∀ (n : ℕ) (ξ ξ' : Ext.{w} (S.obj (op n)) B i),
      ξ.mapExactFunctor (Scheme.Modules.restrictFunctor j.opensRange.ι) =
        ξ'.mapExactFunctor (Scheme.Modules.restrictFunctor j.opensRange.ι) →
      ∃ (m : ℕ) (h : n ≤ m), (Ext.mk₀ (tr S h)).comp ξ (zero_add i) =
        (Ext.mk₀ (tr S h)).comp ξ' (zero_add i)) :
    RestrictionLifting (S ⋙ DerivedCategory.singleFunctor X.Modules p)
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory
      ((DerivedCategory.singleFunctor X.Modules q).obj B) :=
  restrictionLifting_mapDerivedCategory_of_opensRange j _ _
    (restrictionLifting_singleFunctor_of_ext (Scheme.Modules.restrictFunctor j.opensRange.ι)
      S B p q i hi hlift heq)

end AlgebraicGeometry

end
