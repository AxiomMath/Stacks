module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization

/-!
# Lifting an ambient ideal to the ideal sheaf, and the compatibility of open factorizations

[Stacks Project, Tag 01R3] part (2) describes the conormal sheaf of an immersion `i : Z ⟶ X` of
schemes over an affine open `V ⊆ X` on which the scheme-theoretic intersection `Z ∩ V` is
`Spec (Γ(X, V) ⧸ I)`. Every statement of that kind starts from an element `a : I` and needs a
*section of the ideal sheaf* `ℐ_i` over `V` representing it — the hypothesis `he` of the source
says exactly that the ring map `(i)^♯_V : Γ(X, V) ⟶ 𝒪_Z(i⁻¹V)` kills `I`, and the ideal sheaf is
by definition the kernel of the structure-sheaf map.

This file supplies that lift and uses it to identify the quotient map of an arbitrary open
factorization with the factorization-free one on generators, and to reduce the generator property
of part (2) to a single equation mentioning no factorization.

## Main definitions

* `Stacks.Immersion.IsCanonicalAffineGenerators` is the generator property that
  [Stacks Project, Tag 01R3] part (2) asks of its affine identification
  `((i)_* 𝒞_{Z/X})(V) ≅ I/I²`: it quantifies over every closed-immersion factorization of `i` and
  every open of it. A bundled isomorphism of that type asserts nothing without it.

## Main results

* `Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero` is the sectionwise exactness
  of the kernel: a section of `𝒪_X` over an open killed by the structure-sheaf map comes from a
  section of the ideal sheaf. The ideal sheaf is a kernel in `CategoryTheory.SheafOfModules`, and
  `CategoryTheory.SheafOfModules.evaluation` preserves finite limits, so the sections over a fixed
  open are the kernel of the map on sections.
* `Stacks.ClosedImmersion.injective_idealSheafι_val_app` is the other half of the same fact: the
  inclusion of the ideal sheaf is injective on sections over every open.
* `Stacks.Immersion.app_eq_zero_of_mem` is the ring-level content of the hypothesis `he`: the
  ideal `I` lies in the kernel of `(i)^♯_V`.
* `Stacks.Immersion.exists_idealSheaf_section` is the lifting lemma: every `a : I` is the image of
  a section of `ℐ_i` over `V`.
* `Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE` is what this unlocks: the
  quotient map of a closed-immersion factorization of `i` sends a section of `ℐ_{i'}` representing
  an ambient ideal generator `a : I` to the image of the lift of `a` under
  `Stacks.Immersion.canonicalConormalQuotientMap`, which mentions no factorization. That two
  factorizations therefore agree is
  `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_restrict_factorization`.
* `Stacks.Immersion.isCanonicalAffineGenerators_of_apply_eq_canonical` collapses the whole
  quantification in `Stacks.Immersion.IsCanonicalAffineGenerators` to one equation over `V`:
  that `c.inv` carries `I.toCotangent a` to the image of the section of `ℐ_i` representing `a`
  under `Stacks.Immersion.canonicalConormalQuotientMap`.

## Implementation notes

The lifting lemma needs no hypothesis on `i` beyond `he` itself: `i` is not assumed to be an
immersion, let alone a closed one. Both the ring-level step and the kernel step are available for
an arbitrary morphism of schemes, and that is how they are stated.

The ring-level step is the two identities
`Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop` — which routes `(i)^♯_V` through
`Spec Γ(X, V)` — and `Stacks.Immersion.morphismRestrict_comp_isoSpec`, which turns `he` into a
factorization of `i ∣_ V` through `Spec (Γ(X, V) ⧸ I)`. Composing them exhibits `(i)^♯_V`,
followed by an isomorphism, as a map that factors through `Ideal.Quotient.mk I`, and that kills
`a`. The isomorphism is cancelled by composing with its inverse rather than by an injectivity
argument, because the two opens involved, `i ⁻¹ᵁ V` and `(i ⁻¹ᵁ V).ι ''ᵁ ⊤`, are equal but not
syntactically so.

`CategoryTheory.SheafOfModules.evaluation` has no `PreservesZeroMorphisms` instance in Mathlib,
although it has `PreservesFiniteLimits`; without the former, `CategoryTheory.Limits.kernel` of
the evaluated map cannot even be formed. The instance is recorded below; evaluation does not
change the maps on sections, so it is `rfl`.

The sectionwise injectivity is deliberately *not* obtained from
`CategoryTheory.Functor.PreservesMonomorphisms` of the evaluation functor: in this import closure
the instance search for that class resolves through a declaration that is not axiom-clean, as
recorded at `StacksDraft.Ch19.Sec8.Tag01DS`. Factoring the evaluated inclusion as
`CategoryTheory.Limits.PreservesKernel.iso` followed by
`CategoryTheory.Limits.kernel.ι` of the evaluated map, and using
`CategoryTheory.ModuleCat.mono_iff_injective` on the latter, avoids it.

The generator identification is then assembled from three facts in the library and nothing else: the
lift `y` of `a` to `ℐ_i(V)`, the comparison `Stacks.Immersion.idealSheafComparison` whose
composite with the ideal-sheaf inclusion is plain restriction of sections
(`Stacks.Immersion.idealSheafComparison_comp_ι`), and
`Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison`, which says each
factorization's quotient map is the factorization-free
`Stacks.Immersion.canonicalConormalQuotientMap` read through that comparison. Sectionwise
injectivity of the ideal-sheaf inclusion identifies the given `x` with the restriction of the
comparison of `y`, which is the only step where the hypothesis relating `x` to `a` is used. No
affine computation enters: the affine open `V` and the hypothesis `he` are used *only* to produce
`y`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion.AffineConormal Stacks.ClosedImmersion.IdealSheafAffine

universe v u

namespace CategoryTheory.SheafOfModules

/-- **Evaluating a sheaf of modules on a fixed object preserves zero morphisms.** Evaluation does
not change the maps on sections, only forgets all but one of them, so the zero morphism goes to
the zero morphism by definition.

Mathlib has `CategoryTheory.SheafOfModules.evaluationPreservesFiniteLimits` but not this, and
without it `CategoryTheory.Limits.kernel` of an evaluated morphism cannot be formed, so none of
the preservation statements can be used. -/
instance evaluation_preservesZeroMorphisms {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (W : Cᵒᵖ) :
    (SheafOfModules.evaluation.{v} R W).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end CategoryTheory.SheafOfModules

namespace Stacks.ClosedImmersion

/-- The evaluated ideal-sheaf inclusion is `PreservesKernel.iso` followed by `kernel.ι`. -/
private theorem preservesKernel_iso_hom_comp_ι {Z X : RingedSpace.{u, u}} (j : Z ⟶ X)
    (W : Opens X.carrier) :
    (PreservesKernel.iso (SheafOfModules.evaluation.{u} (structureSheafRing X) (op W))
        (structureSheafModuleHom j)).hom ≫
      kernel.ι ((SheafOfModules.evaluation.{u} (structureSheafRing X) (op W)).map
        (structureSheafModuleHom j)) =
      (idealSheafι j).val.app (op W) := by
  rw [← PreservesKernel.iso_inv_ι (SheafOfModules.evaluation.{u} (structureSheafRing X) (op W))
    (structureSheafModuleHom j), Iso.hom_inv_id_assoc]
  rfl

/-- **Sectionwise exactness of the ideal sheaf.** A section of `𝒪_X` over an open `V` that the
structure-sheaf map of `j : Z ⟶ X` sends to zero is the image of a section of the ideal sheaf
`ℐ_j` over `V`.

The ideal sheaf is the kernel of the structure-sheaf map in
`CategoryTheory.SheafOfModules (structureSheafRing X)`, and
`CategoryTheory.SheafOfModules.evaluation` at `V` preserves finite limits, so
`CategoryTheory.Limits.PreservesKernel.iso` identifies the sections of `ℐ_j` over `V` with the
kernel of the map on sections, which `CategoryTheory.ModuleCat.kernelIsoKer` computes as a
submodule. -/
theorem exists_idealSheaf_section_of_app_eq_zero {Z X : RingedSpace.{u, u}} (j : Z ⟶ X)
    (V : Opens X.carrier) (a : (SheafOfModules.unit (structureSheafRing X)).val.obj (op V))
    (ha : (structureSheafModuleHom j).val.app (op V) a = 0) :
    ∃ y : (idealSheaf j).val.obj (op V), (idealSheafι j).val.app (op V) y = a := by
  have hmem : a ∈ LinearMap.ker
      ((SheafOfModules.evaluation.{u} (structureSheafRing X) (op V)).map
        (structureSheafModuleHom j)).hom := ha
  refine ⟨(PreservesKernel.iso (SheafOfModules.evaluation.{u} (structureSheafRing X) (op V))
    (structureSheafModuleHom j)).inv
      ((ModuleCat.kernelIsoKer ((SheafOfModules.evaluation.{u} (structureSheafRing X) (op V)).map
        (structureSheafModuleHom j))).inv ⟨a, hmem⟩), ?_⟩
  refine (congr($(preservesKernel_iso_hom_comp_ι j V) _)).symm.trans ?_
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact congr($(ModuleCat.kernelIsoKer_inv_kernel_ι
    ((SheafOfModules.evaluation.{u} (structureSheafRing X) (op V)).map (structureSheafModuleHom j)))
      (⟨a, hmem⟩ : LinearMap.ker ((SheafOfModules.evaluation.{u} (structureSheafRing X) (op V)).map
        (structureSheafModuleHom j)).hom))

/-- **The inclusion of the ideal sheaf is injective on sections.** Over every open, the map from
the sections of `ℐ_j` to the sections of `𝒪_X` is injective; together with
`Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero` this says the sections of the
ideal sheaf over an open are exactly the sections of `𝒪_X` killed by the structure-sheaf map.

The evaluated inclusion factors as `CategoryTheory.Limits.PreservesKernel.iso` followed by
`CategoryTheory.Limits.kernel.ι` of the evaluated structure-sheaf map; the first is an
isomorphism and the second is a monomorphism of `CategoryTheory.ModuleCat`, hence injective by
`CategoryTheory.ModuleCat.mono_iff_injective`. Deriving the statement instead from
`CategoryTheory.Functor.PreservesMonomorphisms` of the evaluation functor would be unsound here;
see the module docstring. -/
theorem injective_idealSheafι_val_app {Z X : RingedSpace.{u, u}} (j : Z ⟶ X)
    (W : Opens X.carrier) : Function.Injective ((idealSheafι j).val.app (op W)) := by
  intro y y' h
  have h2 := (congr($(preservesKernel_iso_hom_comp_ι j W) y)).trans
    (h.trans (congr($(preservesKernel_iso_hom_comp_ι j W) y')).symm)
  exact (ConcreteCategory.bijective_of_isIso
      (PreservesKernel.iso (SheafOfModules.evaluation.{u} (structureSheafRing X) (op W))
        (structureSheafModuleHom j)).hom).1
    ((ModuleCat.mono_iff_injective _).1 inferInstance h2)

end Stacks.ClosedImmersion

namespace Stacks.Immersion

open Stacks.ClosedImmersion

variable {Z X : Scheme.{u}}

/-! ### The ambient ideal lies in the kernel of the structure-sheaf map -/

/-- **The ring-level content of the hypothesis of [Stacks Project, Tag 01R3] part (2).** If the
scheme-theoretic intersection of `Z` with an affine open `V ⊆ X` is `Spec (Γ(X, V) ⧸ I)`,
compatibly with `V ≅ Spec Γ(X, V)`, then the map `Γ(X, V) ⟶ 𝒪_Z(i⁻¹V)` induced by `i` kills `I`.

The hypothesis `he` is turned into a factorization of the restricted morphism `i ∣_ V` through
`Spec (Γ(X, V) ⧸ I)` by `Stacks.Immersion.morphismRestrict_comp_isoSpec`, and
`Stacks.Immersion.appLE_eq_ΓSpecIso_inv_comp_appTop` reads `(i)^♯_V` through `Spec Γ(X, V)`;
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` then exhibits the composite as
`Ideal.Quotient.mk I` followed by ring maps, and the quotient map kills `a`.

No hypothesis on `i` is needed: it is not assumed to be an immersion. -/
theorem app_eq_zero_of_mem (i : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I)
    (a : Γ(X, V)) (ha : a ∈ I) :
    (i.app V).hom a = 0 := by
  have hz : ((quotImmersion Γ(X, V) I).appTop).hom ((Scheme.ΓSpecIso Γ(X, V)).inv.hom a) = 0 := by
    have h1 := congr($(Scheme.ΓSpecIso_inv_naturality (quotHom I)).hom a)
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h1
    simp only [RingHom.coe_comp, Function.comp_apply] at h1
    rw [← h1, show (quotHom I).hom a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hres : ((i ∣_ V) ≫ hV.isoSpec.hom).appTop =
      (quotImmersion Γ(X, V) I).appTop ≫
        ((pullbackRestrictIsoRestrict i V).symm ≪≫ e).hom.appTop :=
    (congrArg (fun g : (i ⁻¹ᵁ V).toScheme ⟶ Spec Γ(X, V) => g.appTop)
      (morphismRestrict_comp_isoSpec i V hV I e he)).trans (Scheme.Hom.comp_appTop _ _)
  have h0 : (i.app V ≫ Z.presheaf.map (eqToHom (i ⁻¹ᵁ V).ι_image_top).op).hom a = 0 := by
    refine (congr($(appLE_eq_ΓSpecIso_inv_comp_appTop i V hV).hom a)).trans ?_
    rw [CommRingCat.hom_comp]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hres, CommRingCat.hom_comp]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hz, map_zero]
    rfl
  have hm : i.app V ≫ Z.presheaf.map (eqToHom (i ⁻¹ᵁ V).ι_image_top).op ≫
      inv (Z.presheaf.map (eqToHom (i ⁻¹ᵁ V).ι_image_top).op) = i.app V := by
    rw [IsIso.hom_inv_id, Category.comp_id]
  refine (congr($(hm.symm).hom a)).trans ?_
  rw [← Category.assoc, CommRingCat.hom_comp]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [h0, map_zero]

/-! ### The lifting lemma -/

/-- **Every element of the ambient ideal lifts to a section of the ideal sheaf.** Let `i : Z ⟶ X`
be a morphism of schemes, `V ⊆ X` an affine open and `I ⊆ Γ(X, V)` an ideal cutting out the
scheme-theoretic intersection of `Z` with `V`, compatibly with `V ≅ Spec Γ(X, V)`. Then every
`a : I` is the image of a section of the ideal sheaf `ℐ_i` over `V`.

This is `Stacks.Immersion.app_eq_zero_of_mem` — which says `I` lies in the kernel of the
structure-sheaf map on `V` — followed by
`Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero`, the sectionwise exactness of
that kernel. It is what every generator formula of [Stacks Project, Tag 01R3] part (2) needs in
order to speak about `a` at all: the conormal sheaf is built from the ideal sheaf, so a section
of the latter is the only input the quotient map accepts. -/
theorem exists_idealSheaf_section (i : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(X, V)) (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I) (a : I) :
    ∃ y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V),
      (idealSheafι i.toLRSHom.toShHom).val.app (op V) y = (a : Γ(X, V)) :=
  exists_idealSheaf_section_of_app_eq_zero i.toLRSHom.toShHom V (a : Γ(X, V))
    (app_eq_zero_of_mem i V hV I e he (a : Γ(X, V)) a.2)

/-! ### Compatibility of two open factorizations on generators -/

/-- **One factorization's generator is the canonical generator.** For a closed-immersion
factorization `i = i' ≫ ι_U` of an immersion of schemes, an open `W ⊆ U` inside `ι_U⁻¹V` and a
section `x` of `ℐ_{i'}` over `W` whose image in `𝒪_U` is the restriction of `a : I`, the image of
`x` under the quotient map of the factorization agrees, over any open `T ⊆ (i')⁻¹W` of `Z`, with
the image of the lift `y` of `a` under
`Stacks.Immersion.canonicalConormalQuotientMap`, which mentions no factorization.

Sectionwise injectivity of the ideal-sheaf inclusion
(`Stacks.ClosedImmersion.injective_idealSheafι_val_app`) identifies `x` with the restriction to
`W` of the comparison of `y` along `Stacks.Immersion.idealSheafComparison`, because
`Stacks.Immersion.idealSheafComparison_comp_ι` says that comparison is plain restriction of
sections inside `𝒪`; then
`Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison` is exactly the claim. -/
theorem conormalQuotientMap_apply_eq_canonical_of_appLE (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
    (I : Ideal Γ(X, V)) (a : I) (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V)
    (x : (idealSheaf i'.toLRSHom.toShHom).val.obj (op W))
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V))
    (hy : (idealSheafι i.toLRSHom.toShHom).val.app (op V) y = (a : Γ(X, V)))
    (hx : (U.ι.appLE V W hW).hom (a : Γ(X, V)) =
      (idealSheafι i'.toLRSHom.toShHom).val.app (op W) x)
    (T : Z.Opens) (hT : T ≤ i' ⁻¹ᵁ W) (hTV : T ≤ i ⁻¹ᵁ V) :
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE hT).op
        ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op W) x) =
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE hTV).op
        ((canonicalConormalQuotientMap i).val.app (op V) y) := by
  have hTW : T ≤ i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) := hT.trans (i'.preimage_mono hW)
  -- the comparison of `y` maps to the restriction of `a` inside `𝒪_U`
  have hκ : (idealSheafι i'.toLRSHom.toShHom).val.app (op (U.ι ⁻¹ᵁ V))
        ((idealSheafComparison i U i' hfac).val.app (op V) y) =
      (U.ι.app V).hom ((idealSheafι i.toLRSHom.toShHom).val.app (op V) y) :=
    congr($(idealSheafComparison_comp_ι i U i' hfac).val.app (op V) y)
  -- `x` is the restriction to `W` of the comparison of `y`
  have hcomp : x = (idealSheaf i'.toLRSHom.toShHom).val.map (homOfLE hW).op
      ((idealSheafComparison i U i' hfac).val.app (op V) y) := by
    refine injective_idealSheafι_val_app i'.toLRSHom.toShHom W (hx.symm.trans ?_)
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply
      (idealSheafι i'.toLRSHom.toShHom).val (homOfLE hW).op
        ((idealSheafComparison i U i' hfac).val.app (op V) y)).symm
    rw [hκ, hy, Scheme.Hom.appLE, CommRingCat.hom_comp]
    rfl
  -- naturality of the quotient map moves the restriction outside
  have hnat : (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op W)
        ((idealSheaf i'.toLRSHom.toShHom).val.map (homOfLE hW).op
          ((idealSheafComparison i U i' hfac).val.app (op V) y)) =
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (i'.preimage_mono hW)).op
          ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op (U.ι ⁻¹ᵁ V))
            ((idealSheafComparison i U i' hfac).val.app (op V) y)) :=
    PresheafOfModules.naturality_apply (Stacks.Conormal.conormalQuotientMap i U i' hfac).val
      (homOfLE hW).op _
  have hop : (homOfLE (i'.preimage_mono hW)).op ≫ (homOfLE hT).op = (homOfLE hTW).op := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  rw [hcomp, hnat]
  refine Eq.trans ?_ (conormalQuotientMap_apply_idealSheafComparison i U i' hfac V T hTV hTW y)
  refine ((conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map_comp_apply
    (homOfLE (i'.preimage_mono hW)).op (homOfLE hT).op _).symm.trans ?_
  exact (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.congr_map_apply hop _

/-! ### The affine generator property, and its reduction to one equation -/

/-- **The affine generator property of [Stacks Project, Tag 01R3] part (2).** A candidate
identification `c : ((i)_* 𝒞_{Z/X})(V) ≅ I/I²` over an affine open `V ⊆ X` *has the canonical
generators* when, for every closed-immersion factorization `i = i' ≫ ι_U`, every open `W ⊆ U`
inside `ι_U⁻¹V` and every section `x` of `ℐ_{i'}` over `W` representing the restriction of
`a : I`, the class `I.toCotangent a` goes under `c.inv` to the image of `x` under the quotient
map of that factorization.

This is the property that makes the affine computation of [Stacks Project, Tag 01R3] part (2) a
statement and not merely a bundled isomorphism: an arbitrary iso of the same type asserts
nothing. It quantifies over *all* factorizations and *all* opens, and that is what
`Stacks.Immersion.isCanonicalAffineGenerators_of_apply_eq_canonical` collapses. -/
def IsCanonicalAffineGenerators (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) (I : Ideal Γ(X, V))
    (c : ((modulePushforward i.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op V) ≅
      ModuleCat.of Γ(X, V) I.Cotangent) : Prop :=
  ∀ (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V) (a : I)
    (x : (idealSheaf i'.toLRSHom.toShHom).val.obj (op W)),
    (U.ι.appLE V W hW).hom (a : Γ(X, V)) =
      (idealSheafι i'.toLRSHom.toShHom).val.app (op W) x →
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (show i' ⁻¹ᵁ W ≤ i ⁻¹ᵁ V from by
          rw [← hfac]; exact i'.preimage_mono hW)).op (c.inv.hom (I.toCotangent a)) =
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op W) x

/-- **The affine generator property is a single equation.** For an affine open `V ⊆ X` whose
scheme-theoretic intersection with `Z` is `Spec (Γ(X, V) ⧸ I)`, a candidate identification `c`
has the canonical generators of [Stacks Project, Tag 01R3] part (2) as soon as `c.inv` carries
`I.toCotangent a` to the image of *the* section of `ℐ_i` over `V` representing `a` under the
factorization-free `Stacks.Immersion.canonicalConormalQuotientMap`.

So the quantification over every closed factorization and every open in
`Stacks.Immersion.IsCanonicalAffineGenerators` costs nothing: it is equivalent to one equation
over `V` itself, mentioning no factorization. That is
`Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE`, with the restriction to
`T = (i')⁻¹W` taken to be the identity.

The hypothesis is stated for an arbitrary representing section `y` rather than for a chosen one,
which costs nothing either: by
`Stacks.ClosedImmersion.injective_idealSheafι_val_app` there is at most one, and by
`Stacks.Immersion.exists_idealSheaf_section` there is at least one. -/
theorem isCanonicalAffineGenerators_of_apply_eq_canonical (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I)
    (c : ((modulePushforward i.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op V) ≅
      ModuleCat.of Γ(X, V) I.Cotangent)
    (hc : ∀ (a : I) (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V)),
      (idealSheafι i.toLRSHom.toShHom).val.app (op V) y = (a : Γ(X, V)) →
      c.inv.hom (I.toCotangent a) = (canonicalConormalQuotientMap i).val.app (op V) y) :
    IsCanonicalAffineGenerators i V I c := by
  intro U i' _ hfac W hW a x hx
  obtain ⟨y, hy⟩ := exists_idealSheaf_section i V hV I e he a
  have hTV : i' ⁻¹ᵁ W ≤ i ⁻¹ᵁ V := by
    rw [← hfac]
    exact i'.preimage_mono hW
  rw [hc a y hy]
  refine (conormalQuotientMap_apply_eq_canonical_of_appLE i V I a U i' hfac W hW x y hy hx
    (i' ⁻¹ᵁ W) le_rfl hTV).symm.trans ?_
  exact congr($((conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map_id (op (i' ⁻¹ᵁ W)))
    ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (op W) x))

end Stacks.Immersion

end
