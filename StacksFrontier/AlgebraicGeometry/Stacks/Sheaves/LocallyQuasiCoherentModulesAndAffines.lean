module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineModuleExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesEtaleRefinements

/-!
# Locally quasi-coherent modules and affines, for a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, with affine subcategory
`𝒳_{affine}` of Stacks 0H0A and structure sheaf `𝒪`, the restriction of the structure sheaf of
Stacks 06TV to `𝒳_{affine}` (Stacks 0H08). Stacks 0H0F says that for an `𝒪`-module `𝓕` on
`𝒳_{affine}` the following are equivalent:

1. for every arrow `x ⟶ x'` of `𝒳_{affine}` lying over an étale morphism of affine schemes, the
   map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an isomorphism;
2. `𝓕` is a sheaf for the étale topology on `𝒳_{affine}` and, for every object `x` of
   `𝒳_{affine}` lying over `U = p(x)`, the restriction `x^*𝓕|_{U_{affine, étale}}` is
   quasi-coherent;
3. `𝓕` corresponds to a locally quasi-coherent module on `𝒳` (Stacks 06WJ) under the
   equivalence of Stacks 0H0C for the étale topology.

This file proves the three conditions equivalent:
`AlgebraicGeometry.Stack.tfae_locallyQuasicoherent_affine`.

## The proof

* (1) ⇒ (2). The sheaf condition is flat descent along the étale coverings of `𝒳_{affine}`, which
  only uses the cartesian condition along arrows lying over étale morphisms:
  `AlgebraicGeometry.Stack.isSheaf_of_isEtaleCartesian`. Every morphism of `U_{affine, étale}` is
  sent by the affine chart functor to such an arrow, so each chart `x^*𝓕|_{U_{affine, étale}}` is
  cartesian, hence a sheaf and quasi-coherent, by Stacks 0GZX (1) ⇒ (2).
* (2) ⇒ (1). A quasi-coherent chart is cartesian, by Stacks 0H04 on `U_{affine, étale}`. An arrow
  `x ⟶ x'` lying over an étale morphism is isomorphic, as an arrow, to the image under the chart
  functor at `x'` of the morphism from its chart to the final object of `U'_{affine, étale}`, and
  being cartesian is invariant under isomorphism of arrows.
* (3) ⇒ (1). The same argument at the restriction `x'^*𝓖|_{U'_{étale}}` of Stacks 06WJ of the
  locally quasi-coherent module `𝓖`, which is quasi-coherent and therefore cartesian between affine
  objects by Descent, Proposition 03DX (2).
* (1) ⇒ (3). Since `𝓕` is an étale sheaf by (1) ⇒ (2), it is the restriction of a sheaf of
  modules `𝓖` on `𝒳_{étale}`, by the comparison lemma for the dense subsite `𝒳_{affine, étale}` of
  `𝒳_{étale}` (Stacks 0H0B, 0H0C), which holds at the universe of the schemes because the slices
  of `𝒳` are essentially small. For
  every object `x` of `𝒳`, not only the affine ones, `x^*𝓖|_{U_{étale}}` is cartesian between
  affine objects, since the index functor of Stacks 06W1 sends a morphism of affine objects of
  `U_{étale}` to an arrow of `𝒳_{affine}` lying over an étale morphism; so it is quasi-coherent, by
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`.

## Implementation notes

An `𝒪`-module on `𝒳_{affine}` is a presheaf of modules: `𝒳_{affine}` carries the chaotic topology
of Stacks 0H09, for which every presheaf is a sheaf. Condition (3) is read as the corresponding
condition (8) of Stacks 0H0E is: the equivalence of ringed topoi of Stacks 0H0C has restriction
along the affine inclusion for its inverse image, so `𝓕` corresponds to a module `𝓖` on `𝒳`
exactly when `𝓕` is isomorphic to the restriction of `𝓖`.

## References

* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-! ### Condition (1) and the charts -/

/-- **Condition (1) of Stacks 0H0F.** For every arrow `x ⟶ x'` of the affine subcategory lying over
an étale morphism of affine schemes, the base-change map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an
isomorphism. -/
abbrev IsEtaleCartesian
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p)) : Prop :=
  ∀ ⦃y y' : AffineCategory B S hS p⦄ (f : y ⟶ y'),
    Etale ((p ⋙ BigFppfOver.toScheme B S hS).map f.hom) →
      IsIso (restrictionBaseChange.{v, w, u, u} (R := affineStructureCommPresheaf B S hS p) F f.op)

/-- Under condition (1), each chart `x^*𝓕|_{U_{affine, étale}}` is cartesian: the affine chart
functor sends every morphism of `U_{affine, étale}` to an arrow lying over an étale morphism. -/
theorem isIso_restrictionBaseChange_affineChartModule (x : AffineCategory B S hS p)
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (hF : IsEtaleCartesian B S hS p F)
    {V V' : (SmallAffineEtale E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj))ᵒᵖ}
    (a : V ⟶ V') :
    IsIso (restrictionBaseChange.{u + 1, u, u, u}
        (R := SmallEtale.affineChartRings E _ _) (affineChartModule B E h S hS p hp x F) a) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  refine (bijective_restrictionBaseChange_affineChartModule_iff B E h S hS p hp x F a.unop).2 ?_
  refine (ConcreteCategory.isIso_iff_bijective _).1 ?_
  exact hF _ (etale_etaleIndex_map B E h S hS p hp x.obj
    ((SmallAffineEtale.inclusion E _ _).map a.unop))

/-- A quasi-coherent chart `x^*𝓕|_{U_{affine, étale}}` is cartesian, by Stacks 0H04 on
`U_{affine, étale}`. -/
theorem isIso_restrictionBaseChange_affineChartModule_of_isQuasicoherentOnSite
    (x : AffineCategory B S hS p)
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (hM : Presheaf.IsSheaf
      (SmallAffineEtale.topology E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj))
      (affineChartModule B E h S hS p hp x F).presheaf)
    (hqc : (⟨affineChartModule B E h S hS p hp x F, hM⟩ : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite E (p.obj x.obj).left.1
        (contains_base B E h S hS p x.obj)).O)).IsQuasicoherentOnSite)
    {V V' : (SmallAffineEtale E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj))ᵒᵖ}
    (a : V ⟶ V') :
    IsIso (restrictionBaseChange.{u + 1, u, u, u}
      (R := SmallEtale.affineChartRings E _ _) (affineChartModule B E h S hS p hp x F) a) :=
  SmallEtale.isIso_restrictionBaseChange_smallAffineEtale_of_isQuasicoherentOnSite
    E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj)
    (affineChartModule B E h S hS p hp x F) hM hqc a

/-- The chart of an arrow of the affine subcategory lying over an étale morphism, as an object of
the small affine étale site of the scheme below its target. -/
noncomputable abbrev affineEtaleChart {y y' : AffineCategory B S hS p} (f : y ⟶ y')
    (hf : Etale ((p ⋙ BigFppfOver.toScheme B S hS).map f.hom)) :
    SmallAffineEtale E (p.obj y'.obj).left.1 (contains_base B E h S hS p y'.obj) :=
  ⟨etaleChart B E h S hS p f.hom hf, y.property⟩

/-- The final object of the small affine étale site of the scheme below an affine object. -/
noncomputable abbrev affineEtaleTop (y' : AffineCategory B S hS p) :
    SmallAffineEtale E (p.obj y'.obj).left.1 (contains_base B E h S hS p y'.obj) :=
  ⟨etaleTop B E h S hS p y'.obj, y'.property⟩

/-- **Condition (1) from cartesian charts.** If every chart `x^*𝓕|_{U_{affine, étale}}` is
cartesian, then `𝓕` satisfies condition (1): an arrow `x ⟶ x'` over an étale morphism is
isomorphic, as an arrow of `𝒳_{affine}`, to the image under the chart functor at `x'` of the
morphism from its chart to the final object. -/
theorem isEtaleCartesian_of_isIso_affineChartModule
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (hF : ∀ (x : AffineCategory B S hS p)
      {V V' : (SmallAffineEtale E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj))ᵒᵖ}
      (a : V ⟶ V'), IsIso (restrictionBaseChange.{u + 1, u, u, u}
        (R := SmallEtale.affineChartRings E _ _) (affineChartModule B E h S hS p hp x F) a)) :
    IsEtaleCartesian B S hS p F := by
  intro y y' f hf
  obtain ⟨e₁, e₂, hsq⟩ := exists_arrowIso_etaleIndex B E h S hS p hp f.hom hf
  let a : affineEtaleChart B E h S hS p f hf ⟶ affineEtaleTop B E h S hS p y' :=
    ObjectProperty.homMk (etaleChartToTop B E h S hS p f.hom hf)
  have ha := (bijective_restrictionBaseChange_affineChartModule_iff B E h S hS p hp y' F a).1
    ((ConcreteCategory.isIso_iff_bijective _).1 (hF y' a.op))
  let e₁' : y ≅ (affineChart B E h S hS p hp y').obj (affineEtaleChart B E h S hS p f hf) :=
    ObjectProperty.isoMk _ e₁
  let e₂' : y' ≅ (affineChart B E h S hS p hp y').obj (affineEtaleTop B E h S hS p y') :=
    ObjectProperty.isoMk _ e₂
  have hsq' : f ≫ e₂'.hom = e₁'.hom ≫ (affineChart B E h S hS p hp y').map a :=
    ObjectProperty.hom_ext _ hsq
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  refine (bijective_restrictionBaseChange_iff_of_arrowIso F
    ((affineChart B E h S hS p hp y').map a).op f.op e₂'.hom.op e₁'.hom.op ?_).1 ha
  rw [← op_comp, ← op_comp, hsq']

/-! ### The étale sheaf condition -/

include hp in
/-- **Condition (1) implies the étale sheaf condition.** The coverings of `𝒳_{affine, étale}` are
refined by finite families lying over étale coverings of affine schemes, and flat descent along
such a family only uses the cartesian condition along arrows lying over étale morphisms. -/
theorem isSheaf_of_isEtaleCartesian
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (hF : IsEtaleCartesian B S hS p F) :
    Presheaf.IsSheaf
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
      F.presheaf := by
  have := AffineCategory.hasPullbacks B S hS p hp
  have := AffineCategory.preservesPullbacks_toScheme B S hS p hp
  refine isSheaf_of_isIso_restrictionBaseChange_of_etale_refinements.{u, v, w, u, u, u + 1}
    (AffineCategory.toScheme B S hS p) (affineStructureCommPresheaf B S hS p) ?_ ?_ F
    (fun f hf => hF f hf) _ (fun T hT => AffineCategory.exists_etale_refinement B S hS p hp T hT)
  · intro U E _ hE
    obtain ⟨hcov, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineCategory.toScheme B S hS p))).mp hE
    have : ∀ k, Flat ((AffineCategory.toScheme B S hS p).map (E.f k)) := fun k =>
      (Etale.iff_flat_and_formallyUnramified.mp (het k)).1
    exact Scheme.faithfullyFlat_pi_appTop _
      (fun k => (AffineCategory.toScheme B S hS p).map (E.f k)) hcov
  · intro X Y Z P fst snd a b hpb
    have : IsAffine ((AffineCategory.toScheme B S hS p).obj X) := X.property
    have : IsAffine ((AffineCategory.toScheme B S hS p).obj Y) := Y.property
    have : IsAffine ((AffineCategory.toScheme B S hS p).obj Z) := Z.property
    exact isPushout_appTop_of_isPullback (X := (AffineCategory.toScheme B S hS p).obj X)
      (Y := (AffineCategory.toScheme B S hS p).obj Y)
      (Z := (AffineCategory.toScheme B S hS p).obj Z)
      (hpb.map (AffineCategory.toScheme B S hS p))

/-! ### Extending a sheaf on the affine subcategory to `𝒳` -/

/-- **A sheaf of modules on `𝒳_{affine, étale}` is the restriction of a sheaf of modules on
`𝒳_{étale}`**, at the universe of the schemes: the affine inclusion is a dense subsite (Stacks
0H0B), and restriction of sheaves of modules along it is an equivalence (Stacks 0H0C),
`AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`. -/
theorem exists_restriction_iso_of_isSheaf
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (hF : Presheaf.IsSheaf
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
      F.presheaf) :
    ∃ G : SheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)),
      Nonempty ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G.val ≅
        F) := by
  let J₀ := associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS)
  let J := associatedTopology B S hS p (etaleTopology B)
  let ι := AffineCategory.inclusion B S hS p
  let : ι.IsDenseSubsite J₀ J := isDenseSubsite_affineInclusion_etale B S hS p hp
  let R := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
  let := AffineCategory.isEquivalence_moduleRestriction B S hS p hp J₀ J R
  let N : SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction J₀ J ι R) := ⟨F, hF⟩
  obtain ⟨G, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := Stacks.DenseSubsiteModules.moduleRestriction J₀ J ι R) N
  exact ⟨G, ⟨Iso.refl _ ≪≫ (SheafOfModules.forget _).mapIso e⟩⟩

/-! ### Locally quasi-coherent modules on `𝒳` -/

/-- **Condition (3) implies condition (1), for the restriction itself.** The restriction to
`𝒳_{affine}` of a locally quasi-coherent module is cartesian over every arrow lying over an étale
morphism: at the target `x'`, the restriction of Stacks 06WJ is quasi-coherent, hence cartesian
between affine objects (Descent, Proposition 03DX (2)), and the arrow is isomorphic to the image
of a morphism of affine objects of the small étale site. -/
theorem isIso_restrictionBaseChange_of_isLocallyQuasicoherent
    (G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G)
    {y y' : AffineCategory B S hS p} (f : y ⟶ y')
    (hf : Etale ((p ⋙ BigFppfOver.toScheme B S hS).map f.hom)) :
    IsIso (restrictionBaseChange.{v, w, u, u}
      (R := affineStructureCommPresheaf B S hS p)
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G) f.op) := by
  obtain ⟨hM, hqc⟩ := hG.2 y'.obj
  obtain ⟨e₁, e₂, hsq⟩ := exists_arrowIso_etaleIndex B E h S hS p hp f.hom hf
  have hT : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleChart B E h S hS p f.hom hf)) :=
    y.property
  have hT' : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleTop B E h S hS p y'.obj)) :=
    y'.property
  have h1 := SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite E _ _ _ hqc
    hT hT' (etaleChartToTop B E h S hS p f.hom hf)
  have h2 := (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp G
    y'.obj (etaleChartToTop B E h S hS p f.hom hf)).1 h1
  have h3 := (bijective_restrictionBaseChange_iff_of_arrowIso
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G
    ((etaleIndex B E h S hS p hp y'.obj).map (etaleChartToTop B E h S hS p f.hom hf)).op
    f.hom.op e₂.hom.op e₁.hom.op (by rw [← op_comp, ← op_comp, hsq])).1 h2
  exact (ConcreteCategory.isIso_iff_bijective (restrictionBaseChange.{v, w, u, u}
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G
    f.hom.op)).2 h3

/-- Condition (1) is invariant under isomorphism of modules. -/
theorem isIso_restrictionBaseChange_of_iso_pushforward₀
    (G : PresheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (e : (PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G ≅ F)
    {y y' : AffineCategory B S hS p} (f : y ⟶ y')
    (hG : IsIso (restrictionBaseChange.{v, w, u, u}
      (R := affineStructureCommPresheaf B S hS p)
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G) f.op)) :
    IsIso (restrictionBaseChange.{v, w, u, u} (R := affineStructureCommPresheaf B S hS p) F f.op) :=
  isIso_restrictionBaseChange_of_iso (R := affineStructureCommPresheaf B S hS p) e f.op

/-- **Condition (1) for a restriction gives quasi-coherence at every object of `𝒳`.** If the
restriction of a sheaf of modules `𝓖` on `𝒳` to the affine subcategory satisfies condition (1),
then for every object `x` of `𝒳` the restriction `x^*𝓖|_{U_{étale}}` of Stacks 06WJ is cartesian
between affine objects: the index functor sends a morphism of affine objects to an arrow of
`𝒳_{affine}` lying over an étale morphism. -/
theorem isCartesianOnAffines_restrictModuleToSmallEtale
    (G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p))
    (e : (PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G.val ≅ F)
    (hF : IsEtaleCartesian B S hS p F) (x : 𝒳) :
    SmallEtale.IsCartesianOnAffines E (p.obj x).left.1 (contains_base B E h S hS p x)
      ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) G.val,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G.val G.isSheaf⟩ := by
  intro T T' g hT hT'
  refine (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff B E h S hS p hp G.val
    x g).2 ?_
  let yT : AffineCategory B S hS p :=
    ⟨(etaleIndex B E h S hS p hp x).obj T, isAffine_etaleIndex_obj B E h S hS p hp x T hT⟩
  let yT' : AffineCategory B S hS p :=
    ⟨(etaleIndex B E h S hS p hp x).obj T', isAffine_etaleIndex_obj B E h S hS p hp x T' hT'⟩
  let φ : yT ⟶ yT' := ObjectProperty.homMk ((etaleIndex B E h S hS p hp x).map g)
  have := hF φ (etale_etaleIndex_map B E h S hS p hp x g)
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_of_iso (R := affineStructureCommPresheaf B S hS p) e.symm φ.op)

/-! ### Stacks 0H0F -/

/-- Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `𝓕` a module over the
structure sheaf `𝒪` of the affine subcategory `𝒳_{affine}`. The following are equivalent:

1. for every arrow `x ⟶ x'` of `𝒳_{affine}` lying over an étale morphism of affine schemes, the
   map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an isomorphism;
2. `𝓕` is a sheaf for the étale topology on `𝒳_{affine}` and, for every object `x` of
   `𝒳_{affine}`, the restriction `x^*𝓕|_{U_{affine, étale}}` to the small affine étale site of
   `U = p(x)` is quasi-coherent;
3. `𝓕` corresponds to a locally quasi-coherent module on `𝒳` via the equivalence of Stacks 0H0C
   for the étale topology: it is isomorphic to the restriction to `𝒳_{affine}` of a locally
   quasi-coherent module `𝓖` on `𝒳`. -/
@[stacks 0H0F]
theorem tfae_locallyQuasicoherent_affine
    (F : PresheafOfModules.{u} (affineStructurePresheaf B S hS p)) :
    List.TFAE [
      ∀ ⦃x x' : AffineCategory B S hS p⦄ (f : x ⟶ x'),
        Etale ((p ⋙ BigFppfOver.toScheme B S hS).map f.hom) →
          IsIso (restrictionBaseChange.{v, w, u, u}
            (R := affineStructureCommPresheaf B S hS p) F f.op),
      Presheaf.IsSheaf
          (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
          F.presheaf ∧
        ∀ x : AffineCategory B S hS p,
          ∃ hM : Presheaf.IsSheaf
              (SmallAffineEtale.topology E (p.obj x.obj).left.1 (contains_base B E h S hS p x.obj))
              (affineChartModule B E h S hS p hp x F).presheaf,
            (⟨affineChartModule B E h S hS p hp x F, hM⟩ : SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallAffineEtaleRingedSite E (p.obj x.obj).left.1
                  (contains_base B E h S hS p x.obj)).O)).IsQuasicoherentOnSite,
      ∃ G : PresheafOfModules.{u}
          (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj,
        IsLocallyQuasicoherent B E h S hS p hp G ∧
          Nonempty ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G ≅
            F)] := by
  tfae_have 1 → 2 := by
    intro h1
    refine ⟨isSheaf_of_isEtaleCartesian B S hS p hp F h1, fun x => ?_⟩
    have hcart := fun {V V'} (a : V ⟶ V') =>
      isIso_restrictionBaseChange_affineChartModule B E h S hS p hp x F h1 a
    refine ⟨SmallEtale.isSheaf_of_cartesian_smallAffineEtale E _ _ _ hcart, ?_⟩
    exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ _
      (fun _ _ a => hcart a.op)
  tfae_have 2 → 1 := by
    rintro ⟨-, h2⟩
    refine isEtaleCartesian_of_isIso_affineChartModule B E h S hS p hp F (fun x V V' a => ?_)
    obtain ⟨hM, hqc⟩ := h2 x
    exact isIso_restrictionBaseChange_affineChartModule_of_isQuasicoherentOnSite
      B E h S hS p hp x F hM hqc a
  tfae_have 3 → 1 := by
    rintro ⟨G, hG, ⟨e⟩⟩ x x' f hf
    exact isIso_restrictionBaseChange_of_iso_pushforward₀ B S hS p hp G F e f
      (isIso_restrictionBaseChange_of_isLocallyQuasicoherent B E h S hS p hp G hG f hf)
  tfae_have 1 → 3 := by
    intro h1
    obtain ⟨G, ⟨e⟩⟩ := exists_restriction_iso_of_isSheaf B S hS p hp F
      (isSheaf_of_isEtaleCartesian B S hS p hp F h1)
    refine ⟨G.val, ⟨G.isSheaf, fun x =>
      ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G.val G.isSheaf, ?_⟩⟩, ⟨e⟩⟩
    exact SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
      (isCartesianOnAffines_restrictModuleToSmallEtale B E h S hS p hp G F e h1 x)
  tfae_finish

end AlgebraicGeometry.Stack

end
