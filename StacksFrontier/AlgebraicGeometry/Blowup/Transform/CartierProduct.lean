module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.Scheme.PreimageComp
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Composition

/-!
# Enlarging the centre of a blowup by an effective Cartier divisor

Let `S` be a scheme, let `I` be a quasi-coherent ideal sheaf on `S` and let `D` be an effective
Cartier divisor on `S`. Blowing up `S` in the product `I * D` gives the same `S`-scheme as
blowing up `S` in `I`. Moreover, if `f : X ⟶ S` is a morphism and `F` is a sheaf of
`𝒪_X`-modules with no nonzero local sections supported in `f^{-1}(Supp D)`, then the strict
transform of `F` for the centre `I` and the strict transform of `F` for the centre `I * D`
agree, over the induced identification of the two base changes.

## Main results

* `AlgebraicGeometry.blowUpProductIso_exists`: the two blowups are isomorphic over `S`.

That the induced identification of the two base changes carries the strict transform for
`I * D` to the strict transform for `I` -- part (2) of the tag -- is
`Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_mul` of
`StacksFrontier.AlgebraicGeometry.StrictTransform.DifferentCentres`, which states it without the
quasi-coherence hypothesis this module's copy carried.

## Implementation notes

The first statement is the Stacks proof verbatim: on the blowup of `I` the inverse image of `D`
is still an effective Cartier divisor ([Stacks, Tag 0809],
`AlgebraicGeometry.isPullbackDefined_blowUpToBase`), so blowing it up changes nothing
([Stacks, Tag 0807], `AlgebraicGeometry.isIso_blowUpToBase_of_isEffectiveCartierDivisor`), and
the two-step blowup is the blowup in the product ([Stacks, Tag 080A],
`AlgebraicGeometry.blowUpMulIso`).

The second is an instance of the universal property of the quotient by the supported sections,
`AlgebraicGeometry.Scheme.Modules.exists_cokernelSupportedSectionsIso_of_compl_eq`. The pullback
of the strict transform for `I * D` along the comparison of base changes is an epimorphic
quotient of `pr_X^*F` which becomes an isomorphism off, and has no nonzero local sections
supported in, the inverse image of the exceptional locus for `I * D`; that inverse image is the
union of the exceptional locus for `I` with the inverse image of `Supp D`, and the hypothesis on
`F` says exactly that enlarging the supported-sections submodule by the second set changes
nothing (`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`). Transporting
the hypothesis on `F` from `X` to the base change uses that away from the exceptional locus the
projection of the base change to `X` is an open immersion
(`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst`).

## References

* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Scheme.Modules hiding pullback
open Stacks.StrictTransform

/-- Having no nonzero sections supported in a subset descends from the pullback along the
inclusion of an open `U` to sections over `U` itself: a section of `A` over `U` supported in `Z`
is zero as soon as the pullback of `A` to `U` has no nonzero sections supported in the inverse
image of `Z`. -/
private lemma eq_zero_of_mem_supportedSectionsSubmodule_of_pullback_ι {T : Scheme.{u}}
    (U : T.Opens) (Z : Set T) (A : T.Modules)
    (h : ∀ (U' : U.toScheme.Opens) (t : Γ((Scheme.Modules.pullback U.ι).obj A, U')),
      t ∈ (supportedSectionsSubmodule (U.ι.base ⁻¹' Z)
        ((Scheme.Modules.pullback U.ι).obj A)).toSubmodule.obj (op U') → t = 0)
    (s : Γ(A, U)) (hs : s ∈ (supportedSectionsSubmodule Z A).toSubmodule.obj (op U)) :
    s = 0 := by
  have hrestrict : ∀ (U' : U.toScheme.Opens) (t : Γ(A.restrict U.ι, U')),
      t ∈ (supportedSectionsSubmodule (U.ι.base ⁻¹' Z)
        (A.restrict U.ι)).toSubmodule.obj (op U') → t = 0 :=
    supportedSections_eq_zero_of_mono _ ((restrictFunctorIsoPullback U.ι).app A).hom
      inferInstance h
  have himg : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  rw [mem_supportedSectionsSubmodule_iff] at hs
  have key : (A.restrictAppIso U.ι ⊤).inv (A.presheaf.map (eqToHom himg).op s) = 0 := by
    refine hrestrict ⊤ _ ((mem_supportedSectionsSubmodule_iff _ _ _ _).mpr fun x hx hxZ ↦ ?_)
    refine (ConcreteCategory.bijective_of_isIso
      ((restrictStalkNatIso U.ι x).hom.app A)).injective
      (Eq.trans ?_ (map_zero (ConcreteCategory.hom
        ((restrictStalkNatIso U.ι x).hom.app A))).symm)
    show (ConcreteCategory.hom ((A.restrict U.ι).presheaf.germ ⊤ x hx ≫
      (restrictStalkNatIso U.ι x).hom.app A))
      ((A.restrictAppIso U.ι ⊤).inv (A.presheaf.map (eqToHom himg).op s)) = 0
    rw [ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app U.ι x A hx)]
    show (ConcreteCategory.hom
        (A.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) (U.ι.base x) ⟨x, hx, rfl⟩))
      (A.presheaf.map (eqToHom himg).op s) = 0
    exact (TopCat.Presheaf.germ_res_apply A.presheaf (eqToHom himg) (U.ι.base x) ⟨x, hx, rfl⟩
      s).trans (hs _ _ hxZ)
  refine (ConcreteCategory.bijective_of_isIso (A.presheaf.map (eqToHom himg).op)).injective ?_
  rw [map_zero]
  simpa using congrArg (ConcreteCategory.hom (A.restrictAppIso U.ι ⊤).hom) key

/-- **Transport of the hypothesis of [Stacks, Tag 080H] part (2) to the base change.** If `F`
has no nonzero local sections supported in `f^{-1}(Supp D)`, then its pullback to the base change
`X ×_S S'` along the blowup of `I` has no nonzero local sections supported in the inverse image
of `f^{-1}(Supp D)` over an open disjoint from the exceptional locus. -/
private lemma eq_zero_of_mem_supportedSectionsSubmodule_preimage_support
    {X S : Scheme.{u}} (f : X ⟶ S) (I D : S.IdealSheafData) (F : X.Modules)
    (hF : ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ (supportedSectionsSubmodule (f.base ⁻¹' D.supportSet) F).toSubmodule.obj (op U) →
        s = 0)
    (U : (baseChange f (blowUpToBase I)).Opens)
    (hU : (U : Set (baseChange f (blowUpToBase I))) ∩
      exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I) = ∅)
    (s : Γ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F, U))
    (hs : s ∈ (supportedSectionsSubmodule
      ((pullback.fst f (blowUpToBase I)).base ⁻¹' (f.base ⁻¹' D.supportSet))
      ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F)).toSubmodule.obj
        (op U)) : s = 0 := by
  have hUV : U ≤ exceptionalComplement f (blowUpToBase I) (exceptionalIdeal I) :=
    fun x hx hxE ↦ (Set.eq_empty_iff_forall_notMem.mp hU x) ⟨hx, hxE⟩
  have hcompl : IsOpenImmersion
      ((exceptionalComplement f (blowUpToBase I) (exceptionalIdeal I)).ι ≫
        pullback.fst f (blowUpToBase I)) :=
    isOpenImmersion_exceptionalComplement_ι_comp_fst f I
  have hoi : IsOpenImmersion (U.ι ≫ pullback.fst f (blowUpToBase I)) := by
    rw [← Scheme.homOfLE_ι _ hUV, Category.assoc]
    infer_instance
  refine eq_zero_of_mem_supportedSectionsSubmodule_of_pullback_ι U _ _ ?_ s hs
  intro U' t ht
  refine supportedSections_eq_zero_of_mono _
    ((Scheme.Modules.pullbackComp U.ι (pullback.fst f (blowUpToBase I))).app F).hom
    inferInstance ?_ U' t ht
  intro U'' t'' ht''
  exact supportedSections_eq_zero_of_pullback (U.ι ≫ pullback.fst f (blowUpToBase I))
    (f.base ⁻¹' D.supportSet) F hF U'' t''
    (by rwa [preimage_comp_base])

/-- **The comparison of two strict transforms with different centres.** Let `g` identify the base
change of `f` along `b` with the base change along `b'`, compatibly with the projections to `X`,
and suppose the inverse image of the exceptional locus for `E'` is the exceptional locus for `E`
enlarged by a subset `W` in which `pr_X^*F` has no nonzero local sections over opens disjoint
from the exceptional locus for `E`. Then `g` carries the strict transform for `E'` to the strict
transform for `E`.

The strict transform for `E` is the quotient of `pr_X^*F` by the sections supported in the
exceptional locus for `E`, hence also by the sections supported in its union with `W`; and the
pullback along `g` of the strict transform for `E'` has the universal property of that
quotient. -/
private lemma exists_pullback_sheaf_iso {X S S₁ S₂ : Scheme.{u}} (f : X ⟶ S) (b : S₁ ⟶ S)
    (b' : S₂ ⟶ S) (E : S₁.IdealSheafData) (E' : S₂.IdealSheafData) (F : X.Modules)
    (g : baseChange f b ≅ baseChange f b')
    (hfst : g.hom ≫ pullback.fst f b' = pullback.fst f b) (W : Set (baseChange f b))
    (hsupport : g.hom.base ⁻¹' exceptionalPreimage f b' E' = exceptionalPreimage f b E ∪ W)
    (hW : ∀ U : (baseChange f b).Opens,
      (U : Set (baseChange f b)) ∩ exceptionalPreimage f b E = ∅ →
      ∀ s : Γ((Scheme.Modules.pullback (pullback.fst f b)).obj F, U),
        s ∈ (supportedSectionsSubmodule W
          ((Scheme.Modules.pullback (pullback.fst f b)).obj F)).toSubmodule.obj (op U) → s = 0) :
    Nonempty ((Scheme.Modules.pullback g.hom).obj (sheaf f b' E' F) ≅ sheaf f b E F) := by
  have hcl : IsClosed (exceptionalPreimage f b E) :=
    E.isClosed_supportSet.preimage (by fun_prop)
  have hN : supportedSectionsSubmodule (exceptionalPreimage f b E ∪ W)
        ((Scheme.Modules.pullback (pullback.fst f b)).obj F) =
      supportedSectionsSubmodule (exceptionalPreimage f b E)
        ((Scheme.Modules.pullback (pullback.fst f b)).obj F) :=
    supportedSectionsSubmodule_union_eq _ _ hcl _ hW
  let V : (baseChange f b).Opens := g.hom ⁻¹ᵁ exceptionalComplement f b' E'
  have hVc : exceptionalPreimage f b E ∪ W = (V : Set (baseChange f b))ᶜ := by
    rw [← hsupport, exceptionalPreimage_eq_compl, Set.preimage_compl]
    rfl
  let α : (Scheme.Modules.pullback g.hom).obj
        ((Scheme.Modules.pullback (pullback.fst f b')).obj F) ≅
      (Scheme.Modules.pullback (pullback.fst f b)).obj F :=
    (Scheme.Modules.pullbackComp g.hom (pullback.fst f b')).app F ≪≫
      (Scheme.Modules.pullbackCongr hfst).app F
  have hmono : Mono ((restrictAdjunction V.ι).unit.app
      ((Scheme.Modules.pullback g.hom).obj (sheaf f b' E' F))) := by
    refine mono_unit_app_of_supportedSections_eq_zero V _ ?_
    rw [← hVc, ← hsupport]
    exact supportedSections_eq_zero_of_pullback g.hom (exceptionalPreimage f b' E')
      (sheaf f b' E' F) (supportedSections_sheaf_eq_zero f b' E' F)
  have hπ : IsIso ((restrictFunctor (exceptionalComplement f b' E').ι).map (π f b' E' F)) :=
    isIso_restrictFunctor_map_π f b' E' F
  have hres : IsIso ((restrictFunctor V.ι).map
      ((Scheme.Modules.pullback g.hom).map (π f b' E' F))) :=
    isIso_restrictFunctor_map_pullback_map g.hom (exceptionalComplement f b' E') (π f b' E' F)
  have hmono' : Mono ((restrictFunctor V.ι).map
      (α.inv ≫ (Scheme.Modules.pullback g.hom).map (π f b' E' F))) := by
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨iso, -⟩ := exists_cokernelSupportedSectionsIso_of_compl_eq V hVc
    (α.inv ≫ (Scheme.Modules.pullback g.hom).map (π f b' E' F))
  refine ⟨iso.symm ≪≫ eqToIso ?_⟩
  show cokernel (supportedSectionsSubmodule (exceptionalPreimage f b E ∪ W)
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F)).ι =
    cokernel (supportedSectionsSubmodule (exceptionalPreimage f b E)
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F)).ι
  rw [hN]

/-- **Stacks Project, Tag 080H**, part (1). Let `D` be an effective Cartier divisor on `S` and
let `I` be any quasi-coherent ideal sheaf. The blowup of `S` in `I * D` is the blowup of `S` in
`I`, as `S`-schemes. -/
@[stacks 080H "part (1): isomorphism of blowups"]
theorem blowUpProductIso_exists {S : Scheme.{u}} (I D : S.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Nonempty (Over.mk (blowUpToBase I) ≅ Over.mk (blowUpToBase (I * D))) := by
  have : IsIso (blowUpToBase (D.comap (blowUpToBase I))) :=
    isIso_blowUpToBase_of_isEffectiveCartierDivisor _ (isPullbackDefined_blowUpToBase I D hD)
  have e₁ : Over.mk (blowUpToBase I) ≅
      Over.mk (blowUpToBase (D.comap (blowUpToBase I)) ≫ blowUpToBase I) :=
    Over.isoMk (asIso (blowUpToBase (D.comap (blowUpToBase I)))).symm (Iso.inv_hom_id_assoc _ _)
  exact ⟨e₁ ≪≫ blowUpMulIso I D⟩


end AlgebraicGeometry

end
