module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.BaseChangeChartSolutions

/-!
# The comparison of step (3) of Stacks 04I6 is natural in both variables

Let `(g, g^♯)` be a morphism of the small étale ringed topoi of two schemes `X` and `Y` of a big
étale site, and let `f : X ⟶ Y` be a morphism of schemes whose ring map on global functions is the
one `(g, g^♯)` induces — the morphism chosen in the first paragraph of the proof of
[Stacks Project, Tag 04I6].

For an *affine* étale chart `V` of `Y`, a chart `U` of `X` and a section `s` of `g⁻¹h_V` over `U`,
`AlgebraicGeometry.comparisonRingHom` is a ring homomorphism `Γ(V, ⊤) ⟶ Γ(U, ⊤)`, and
`AlgebraicGeometry.comparisonRingHom_comp_appTop_schemeStructureHom` says that it is compatible
with the structure maps over `Y`.  Since `V` is affine such a ring map *is* a morphism of schemes
`U ⟶ V`, and since `Y` is affine the compatibility *is* the assertion that it commutes over `Y`;
so the pair names a morphism of the small étale site of `X`

`U ⟶ X ×_Y V`.

This file shows that that assignment is **natural in `U`**, so that it is a morphism of sheaves
`g⁻¹h_V ⟶ h_{X ×_Y V}`, and **natural in the affine chart `V`**, so that the morphisms of sheaves
assemble into a natural transformation.  Those are the two halves of the "assembly" which the
"Where the rest of Stacks 04I6 is" section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean` records as
separating the per-chart bijection from `AlgebraicGeometry.RepresentableComparison`.

## The route: the affine adjunction, not the presentation

The existing description of the per-chart map goes through a standard presentation of `V`: the
values of `AlgebraicGeometry.comparisonCoord` solve the presented system
(`AlgebraicGeometry.isSolution_comparisonCoord_globalSectionsMap`) and the solutions are the
sections of `h_{X ×_Y V}` (`AlgebraicGeometry.SmallEtale.baseChangeHomEquivSolutions`).  That
description is what makes the *iso-ness* argument of Stacks 04GX available, but it is not needed to
**construct** the map, and it is actively unhelpful for naturality in `V`: the number `n` of
coordinates and the system `P` are attached to `V`, so a morphism `V ⟶ V'` of charts relates two
unrelated presentations.

What this file uses instead is that a ring map into `Γ(U, ⊤)` out of the global functions on an
*affine* scheme is a morphism of schemes — `Stacks.EtaleCohomology.homOverEquivAppTopOver`, the
relative form of [Stacks Project, Tag 01I1] — composed with the universal property of the
base-changed chart, `AlgebraicGeometry.SmallEtale.baseChangeHomEquiv`.  Both are bijections natural
in everything in sight, and the content of the file is therefore the naturality of
`AlgebraicGeometry.comparisonRingHom` itself, in each of its two variables:

* in `U`, it is the naturality of the morphism of sheaves `g⁻¹h_V ⟶ 𝒪_X` which the section is
  evaluated against — nothing about `g` is used;
* in `V`, it is the naturality of `g^♯` on the small étale site of `Y` together with the naturality
  of the Yoneda ring identification,
  `MorphismOfTopoi.inverseImageYonedaRingEquiv_symm_naturality`.

The two descriptions agree on the nose, so nothing is lost: both the presentation route and this
one send `(U, s)` to the morphism of schemes with ring map `AlgebraicGeometry.comparisonRingHom`,
by `Stacks.EtaleCohomology.homOverEquivSolutions`'s own construction out of
`Stacks.EtaleCohomology.homOverEquivAppTopOver`.

## Main definitions

* `AlgebraicGeometry.comparisonSchemeHom` — the morphism of schemes `U ⟶ V` named by
  `AlgebraicGeometry.comparisonRingHom`, for an affine chart `V`.
* `AlgebraicGeometry.comparisonChartHom` — the morphism `U ⟶ X ×_Y V` of the small étale site of
  `X` which it determines.
* `AlgebraicGeometry.comparisonSheafHom` — **the comparison as a morphism of sheaves**
  `g⁻¹h_V ⟶ h_{X ×_Y V}`, which is the naturality in `U`.

## Main results

* `AlgebraicGeometry.comparisonRingHom_naturality_section` and
  `AlgebraicGeometry.comparisonRingHom_naturality_chart` — naturality of the induced ring
  homomorphism in the chart `U` of `X` and in the affine chart `V` of `Y`.
* `AlgebraicGeometry.comparisonChartHom_naturality_section` — naturality in `U`, at the level of
  the site of `X`.
* `AlgebraicGeometry.comparisonSheafHom_naturality_chart` — **naturality in `V`**: the comparison
  commutes with `g⁻¹h_k` and `h_{X ×_Y k}` for a morphism `k : V ⟶ V'` of affine charts of `Y`.
* `AlgebraicGeometry.exists_schemeHom_appTop_eq_globalSectionsMap` — the hypothesis on `f` carried
  by the constructions here is the source's own choice of `f`, and it is satisfiable: for affine
  `Y` such an `f` exists.  So nothing below is vacuous.

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag.  The comparison here is produced only at the
*affine* charts of `Y`, and is not shown to be an isomorphism; that it is one is
`AlgebraicGeometry.isIso_comparisonSheafHom`, and the tag is
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`.  The
comparison is never produced at a non-affine chart, and does not need to be: what is transported
to all charts is the isomorphism of direct images.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.EtaleCohomology AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

/-! ### The restriction maps of the structure sheaf -/

/-- **The restriction maps of the structure sheaf of the small étale site are the ring maps on
global functions of the underlying morphisms of schemes.**  This is the statement of which
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf_map_from_final` is the special case at the
unique morphism to the terminal chart. -/
theorem SmallEtale.commRingStructureSheaf_map (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U U' : SmallEtale B S hS} (k : U ⟶ U') :
    (SmallEtale.commRingStructureSheaf B S hS).obj.map k.op =
      ((SmallEtale.toScheme B S hS).map k).appTop :=
  Scheme.Γ_map_op ((SmallEtale.toScheme B S hS).map k)

/-! ### Naturality of the induced ring homomorphism -/

section RingHom

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY)))

/-- **The generalized element of `𝒪_X` which a global function on an étale chart `V` of `Y`
determines.**  It is `g^♯` at `V`, read as a map of sheaves `g⁻¹h_V ⟶ 𝒪_X` through the Yoneda ring
identification `MorphismOfTopoi.inverseImageYonedaRingEquiv`.

This is the single map out of which the whole comparison is built: at a standard presentation of
`V` its values on the coordinate functions are `AlgebraicGeometry.comparisonCoord`, and its value
at a section of `g⁻¹h_V` over a chart `U` of `X` is `AlgebraicGeometry.comparisonRingHom`. -/
def comparisonElt (V : SmallEtale B Y hY) (t : Γ((SmallEtale.toScheme B Y hY).obj V, ⊤)) :
    g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V) ⟶
      ringSheaf (smallEtaleRingSheaf B hX) :=
  (inverseImageHomRingEquiv B hX hY g V).symm ((g.fSharp.hom.app (op V)).hom t)

/-- The `i`-th coordinate of the comparison is the generalized element of the `i`-th coordinate
function of the presentation. -/
theorem comparisonCoord_eq_comparisonElt [IsAffine Y] {n : ℕ}
    {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)} (V : SmallEtale B Y hY)
    [IsAffine ((SmallEtale.toScheme B Y hY).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
      (schemeStructureHom B Y hY V) P) (i : Fin n) :
    comparisonCoord B hX hY g V pres i =
      comparisonElt B hX hY g V (presCoord B hY V pres i) :=
  rfl

/-- The ring homomorphism induced by the comparison is the evaluation of
`AlgebraicGeometry.comparisonElt` at the section. -/
theorem comparisonRingHom_apply (V : SmallEtale B Y hY) (U : (SmallEtale B X hX)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V)))
    (t : Γ((SmallEtale.toScheme B Y hY).obj V, ⊤)) :
    comparisonRingHom B hX hY g V U s t =
      (sectionsFunctor (SmallEtale.topology B X hX) U).map
        (comparisonElt B hX hY g V t) s :=
  rfl

/-- **The generalized element is natural in the chart `V` of `Y`.**  Restricting a global function
on `V'` to `V` and taking its generalized element is the same as taking its generalized element on
`V'` and precomposing with `g⁻¹h_k`.

This is the naturality of `g^♯`, which is a morphism of sheaves of rings on the small étale site
of `Y`, together with the naturality of the Yoneda ring identification,
`MorphismOfTopoi.inverseImageYonedaRingEquiv_symm_naturality`. -/
theorem comparisonElt_naturality {V V' : SmallEtale B Y hY} (k : V ⟶ V')
    (t : Γ((SmallEtale.toScheme B Y hY).obj V', ⊤)) :
    g.toToposHom.inverseImage.map ((SmallEtale.topology B Y hY).yoneda.map k) ≫
        comparisonElt B hX hY g V' t =
      comparisonElt B hX hY g V (((SmallEtale.toScheme B Y hY).map k).appTop.hom t) := by
  unfold comparisonElt
  rw [← SmallEtale.commRingStructureSheaf_map B Y hY k]
  refine (MorphismOfTopoi.inverseImageYonedaRingEquiv_symm_naturality
    g.toToposHom (smallEtaleRingSheaf B hX) V V' k
    ((g.fSharp.hom.app (op V')).hom t)).symm.trans ?_
  exact congrArg (inverseImageHomRingEquiv B hX hY g V).symm
    (NatTrans.naturality_apply g.fSharp.hom k.op t).symm

/-- **The ring homomorphism induced by the comparison is natural in the chart `U` of `X`.**
Restricting the section `s` along `k` and then taking the induced ring map is the same as taking
the induced ring map and then restricting its values.

Nothing about `g` is used: the only `U`-dependent ingredient of
`AlgebraicGeometry.comparisonRingHom` is the evaluation of a *morphism of sheaves*
`g⁻¹h_V ⟶ 𝒪_X` at a section, and this is that morphism's naturality. -/
theorem comparisonRingHom_naturality_section (V : SmallEtale B Y hY)
    {U U' : (SmallEtale B X hX)ᵒᵖ} (k : U ⟶ U')
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V)))
    (t : Γ((SmallEtale.toScheme B Y hY).obj V, ⊤)) :
    comparisonRingHom B hX hY g V U'
        ((sectionsRestrict k).app
          (g.toToposHom.inverseImage.obj
            ((SmallEtale.topology B Y hY).yoneda.obj V)) s) t =
      ((SmallEtale.toScheme B X hX).map k.unop).appTop.hom
        (comparisonRingHom B hX hY g V U s t) := by
  have hnat := NatTrans.naturality_apply
    ((inverseImageHomRingEquiv B hX hY g V).symm
      ((g.fSharp.hom.app (op V)).hom t)).hom k s
  rw [← SmallEtale.commRingStructureSheaf_map B X hX k.unop]
  exact hnat

/-- **The ring homomorphism induced by the comparison is natural in the chart `V` of `Y`.**
Pushing the section `s` along `g⁻¹h_k` and then taking the induced ring map `Γ(V', ⊤) ⟶ Γ(U, ⊤)`
is the same as restricting along `k` and then taking the induced ring map out of `Γ(V, ⊤)`.

This is where the two naturalities of the construction are used: that of `g^♯`, which is a
morphism of sheaves of rings on the small étale site of `Y`, and that of the Yoneda ring
identification, `MorphismOfTopoi.inverseImageYonedaRingEquiv_symm_naturality`. -/
theorem comparisonRingHom_naturality_chart {V V' : SmallEtale B Y hY} (k : V ⟶ V')
    (U : (SmallEtale B X hX)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X hX) U).obj
      (g.toToposHom.inverseImage.obj ((SmallEtale.topology B Y hY).yoneda.obj V)))
    (t : Γ((SmallEtale.toScheme B Y hY).obj V', ⊤)) :
    comparisonRingHom B hX hY g V' U
        ((sectionsFunctor (SmallEtale.topology B X hX) U).map
          (g.toToposHom.inverseImage.map ((SmallEtale.topology B Y hY).yoneda.map k)) s) t =
      comparisonRingHom B hX hY g V U s
        (((SmallEtale.toScheme B Y hY).map k).appTop.hom t) := by
  rw [comparisonRingHom_apply, comparisonRingHom_apply, ← Functor.map_comp_apply,
    comparisonElt_naturality]

end RingHom

/-! ### The comparison as a morphism of schemes -/

section SchemeHom

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- **The morphism of schemes `U ⟶ V` named by the comparison.**  Since the chart `V` of `Y` is
affine, the ring homomorphism `Γ(V, ⊤) ⟶ Γ(U, ⊤)` of `AlgebraicGeometry.comparisonRingHom` is a
morphism of schemes, by the affine-target form of [Stacks Project, Tag 01I1]
(`Stacks.EtaleCohomology.schemeHomOfAppTop`). -/
def comparisonSchemeHom (V : SmallEtale B Y.obj Y.property)
    [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    (SmallEtale.toScheme B X.obj X.property).obj U.unop ⟶
      (SmallEtale.toScheme B Y.obj Y.property).obj V :=
  schemeHomOfAppTop _ _
    (CommRingCat.ofHom (comparisonRingHom B X.property Y.property g V U s))

variable (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]

/-- On global functions, the morphism of schemes named by the comparison induces the comparison's
ring homomorphism. -/
@[simp]
theorem appTop_comparisonSchemeHom (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    (comparisonSchemeHom B g V U s).appTop =
      CommRingCat.ofHom (comparisonRingHom B X.property Y.property g V U s) :=
  appTop_schemeHomOfAppTop _ _ _

/-- **Naturality of the comparison in the chart `U` of `X`, as morphisms of schemes.** -/
theorem comparisonSchemeHom_naturality_section
    {U U' : (SmallEtale B X.obj X.property)ᵒᵖ} (k : U ⟶ U')
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    comparisonSchemeHom B g V U'
        ((sectionsRestrict k).app
          (g.toToposHom.inverseImage.obj
            ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)) s) =
      (SmallEtale.toScheme B X.obj X.property).map k.unop ≫
        comparisonSchemeHom B g V U s := by
  refine (schemeHomEquivAppTop _ ((SmallEtale.toScheme B Y.obj Y.property).obj V)).injective ?_
  rw [schemeHomEquivAppTop_apply, schemeHomEquivAppTop_apply, Scheme.Hom.comp_appTop,
    appTop_comparisonSchemeHom, appTop_comparisonSchemeHom]
  refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact comparisonRingHom_naturality_section B X.property Y.property g V k s t

/-- **Naturality of the comparison in the affine chart `V` of `Y`, as morphisms of schemes.** -/
theorem comparisonSchemeHom_naturality_chart
    {V' : SmallEtale B Y.obj Y.property}
    [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')] (k : V ⟶ V')
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    comparisonSchemeHom B g V' U
        ((sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map
          (g.toToposHom.inverseImage.map
            ((SmallEtale.topology B Y.obj Y.property).yoneda.map k)) s) =
      comparisonSchemeHom B g V U s ≫ (SmallEtale.toScheme B Y.obj Y.property).map k := by
  refine (schemeHomEquivAppTop _ ((SmallEtale.toScheme B Y.obj Y.property).obj V')).injective ?_
  rw [schemeHomEquivAppTop_apply, schemeHomEquivAppTop_apply, Scheme.Hom.comp_appTop,
    appTop_comparisonSchemeHom, appTop_comparisonSchemeHom]
  refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact comparisonRingHom_naturality_chart B X.property Y.property g k U s t

/-- **The hypothesis on `f` carried below is the source's own choice of `f`, and it is
satisfiable.**  For an affine `Y` of the big étale site there *is* a morphism `f : X ⟶ Y` of the
site whose ring map on global functions is the one `(g, g^♯)` induces: it is `Spec` of that ring
map (`Stacks.EtaleCohomology.schemeHomOfAppTop`), which lies in the site because the inclusion of
the big étale site into schemes is full.

This is the morphism chosen in the first paragraph of the proof of [Stacks Project, Tag 04I6],
where `Y = Spec B`, `X = Spec A` and `f = Spec φ` for `φ : B ⟶ A` the ring map of `g^♯` on global
sections.  It is recorded so that the hypothesis `hf` below is visibly not vacuous. -/
theorem exists_schemeHom_appTop_eq_globalSectionsMap [IsAffine Y.obj] :
    ∃ f : X ⟶ Y, (B.inclusion.map f).appTop =
      g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
        (SmallEtale.finalIsTerminal B Y.obj Y.property) := by
  refine ⟨B.inclusion.preimage (schemeHomOfAppTop X.obj Y.obj
    (g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))), ?_⟩
  rw [B.inclusion.map_preimage]
  exact appTop_schemeHomOfAppTop X.obj Y.obj _

variable (f : X ⟶ Y)
  (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))

include hf in
/-- **The morphism of schemes named by the comparison commutes over `Y`.**  This is the
coefficient identification `AlgebraicGeometry.comparisonRingHom_comp_appTop_schemeStructureHom`
read through the affine base: since `Y` is affine, a morphism of schemes to `Y` is determined by
its ring map on global functions, so the equality of ring maps *is* the commuting triangle.

The hypothesis `hf` is the choice of `f` made in the first paragraph of the proof of
[Stacks Project, Tag 04I6]: its ring map on global functions is the one `(g, g^♯)` induces. -/
theorem comparisonSchemeHom_comp_schemeStructureHom [IsAffine Y.obj]
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    comparisonSchemeHom B g V U s ≫ schemeStructureHom B Y.obj Y.property V =
      schemeStructureHom B X.obj X.property U.unop ≫ B.inclusion.map f := by
  refine (schemeHomEquivAppTop _ Y.obj).injective ?_
  rw [schemeHomEquivAppTop_apply, schemeHomEquivAppTop_apply, Scheme.Hom.comp_appTop,
    Scheme.Hom.comp_appTop, appTop_comparisonSchemeHom]
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    comparisonRingHom_comp_appTop_schemeStructureHom]
  exact congrArg (fun φ : Γ(Y.obj, ⊤) ⟶ Γ(X.obj, ⊤) =>
    (schemeStructureHom B X.obj X.property U.unop).appTop.hom.comp φ.hom) hf.symm

end SchemeHom

/-! ### The comparison as a morphism of sheaves, natural in the affine chart -/

section SheafHom

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (f : X ⟶ Y)

/-- **Base change of an arrow of charts commutes with the projections.**  For `k : V ⟶ V'` an
arrow of the small étale site of `Y`, the square formed by `X ×_Y k` and the two projections to
`V` and `V'` commutes.  This is `CategoryTheory.Limits.pullback.lift_fst`, since base change of
charts is pullback in the slice category
(`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`). -/
theorem toScheme_map_smallEtaleBaseChange_comp_baseChangeProj
    {V V' : SmallEtale B Y.obj Y.property} (k : V ⟶ V') :
    (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map k) ≫
        SmallEtale.baseChangeProj B f V' =
      SmallEtale.baseChangeProj B f V ≫ (SmallEtale.toScheme B Y.obj Y.property).map k := by
  have h : ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange B f).map k)).left ≫ pullback.fst V'.obj.hom f =
      pullback.fst V.obj.hom f ≫
        ((SmallEtale.inclusion B Y.obj Y.property).map k).left := by
    show ((Over.pullback f).map ((SmallEtale.inclusion B Y.obj Y.property).map k)).left ≫ _ = _
    exact pullback.lift_fst _ _ _
  exact (B.inclusion.map_comp
      ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange B f).map k)).left
      (pullback.fst V'.obj.hom f)).symm.trans
    ((congrArg B.inclusion.map h).trans
      (B.inclusion.map_comp (pullback.fst V.obj.hom f)
        ((SmallEtale.inclusion B Y.obj Y.property).map k).left))

variable (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))
  [IsAffine Y.obj] (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]

include hf in
/-- **The comparison at a chart and a section, as a morphism of the small étale site of `X`.**
The morphism of schemes `U ⟶ V` named by the comparison commutes over `Y`, so by the universal
property of the base-changed chart (`AlgebraicGeometry.SmallEtale.baseChangeHomEquiv`) it names a
morphism `U ⟶ X ×_Y V` of the site. -/
def comparisonChartHom (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    U.unop ⟶ (smallEtaleBaseChange B f).obj V :=
  (SmallEtale.baseChangeHomEquiv B f V U.unop).symm
    ⟨comparisonSchemeHom B g V U s,
      comparisonSchemeHom_comp_schemeStructureHom B g V f hf U s⟩

include hf in
/-- The morphism of schemes underlying `AlgebraicGeometry.comparisonChartHom`, followed by the
projection of the base-changed chart, is `AlgebraicGeometry.comparisonSchemeHom`. -/
@[simp]
theorem toScheme_map_comparisonChartHom_comp_baseChangeProj
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    (SmallEtale.toScheme B X.obj X.property).map (comparisonChartHom B g f hf V U s) ≫
        SmallEtale.baseChangeProj B f V = comparisonSchemeHom B g V U s := by
  have h := congrArg Subtype.val ((SmallEtale.baseChangeHomEquiv B f V U.unop).apply_symm_apply
    ⟨comparisonSchemeHom B g V U s,
      comparisonSchemeHom_comp_schemeStructureHom B g V f hf U s⟩)
  rwa [SmallEtale.baseChangeHomEquiv_apply_coe] at h

include hf in
/-- **Naturality of the comparison in the chart `U` of `X`.**  This is what makes the comparison a
morphism of *sheaves* `g⁻¹h_V ⟶ h_{X ×_Y V}` rather than a family of maps on sections. -/
theorem comparisonChartHom_naturality_section
    {U U' : (SmallEtale B X.obj X.property)ᵒᵖ} (k : U ⟶ U')
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    comparisonChartHom B g f hf V U'
        ((sectionsRestrict k).app
          (g.toToposHom.inverseImage.obj
            ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)) s) =
      k.unop ≫ comparisonChartHom B g f hf V U s := by
  refine (SmallEtale.baseChangeHomEquiv B f V U'.unop).injective (Subtype.ext ?_)
  rw [SmallEtale.baseChangeHomEquiv_apply_coe, SmallEtale.baseChangeHomEquiv_apply_coe,
    CategoryTheory.Functor.map_comp, Category.assoc,
    toScheme_map_comparisonChartHom_comp_baseChangeProj,
    toScheme_map_comparisonChartHom_comp_baseChangeProj]
  exact comparisonSchemeHom_naturality_section B g V k s

include hf in
/-- **Naturality of the comparison in the affine chart `V` of `Y`.**  This is what makes the
morphisms of sheaves assemble into a natural transformation. -/
theorem comparisonChartHom_naturality_chart
    {V' : SmallEtale B Y.obj Y.property}
    [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')] (k : V ⟶ V')
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    comparisonChartHom B g f hf V' U
        ((sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map
          (g.toToposHom.inverseImage.map
            ((SmallEtale.topology B Y.obj Y.property).yoneda.map k)) s) =
      comparisonChartHom B g f hf V U s ≫ (smallEtaleBaseChange B f).map k := by
  refine (SmallEtale.baseChangeHomEquiv B f V' U.unop).injective (Subtype.ext ?_)
  rw [SmallEtale.baseChangeHomEquiv_apply_coe, SmallEtale.baseChangeHomEquiv_apply_coe,
    CategoryTheory.Functor.map_comp, Category.assoc,
    toScheme_map_smallEtaleBaseChange_comp_baseChangeProj, ← Category.assoc,
    toScheme_map_comparisonChartHom_comp_baseChangeProj,
    toScheme_map_comparisonChartHom_comp_baseChangeProj]
  exact comparisonSchemeHom_naturality_chart B g V k U s

include hf in
/-- **The comparison of step (3) of Stacks 04I6, as a morphism of sheaves.**  For an affine chart
`V` of an affine `Y`,

`g⁻¹h_V ⟶ h_{X ×_Y V}`,

the value at a section `s` over a chart `U` of `X` being the morphism `U ⟶ X ×_Y V` whose ring map
on global functions is `AlgebraicGeometry.comparisonRingHom`.

This is the map the source constructs; what remains of the tag is that it is an *isomorphism*
(the stalk computation, using [Stacks Project, Tag 04GX]) and that it is available at every chart
of `Y` and not only the affine ones ([Stacks Project, Tag 04HR]). -/
def comparisonSheafHom :
    g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V) ⟶
      (SmallEtale.topology B X.obj X.property).yoneda.obj
        ((smallEtaleBaseChange B f).obj V) :=
  ⟨{ app := fun U => TypeCat.ofHom fun s => comparisonChartHom B g f hf V U s
     naturality := fun U U' k => by
       apply TypeCat.homEquiv.injective
       funext s
       simp only [TypeCat.homEquiv_apply, TypeCat.ofHom_apply, types_comp_apply]
       exact comparisonChartHom_naturality_section B g f hf V k s }⟩

include hf in
/-- On sections over a chart `U` of `X`, the comparison morphism
`AlgebraicGeometry.comparisonSheafHom` sends a section `s` to
`AlgebraicGeometry.comparisonChartHom` applied to `s`. -/
@[simp]
theorem comparisonSheafHom_app_apply (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).obj
      (g.toToposHom.inverseImage.obj
        ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V))) :
    (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map
        (comparisonSheafHom B g f hf V) s =
      comparisonChartHom B g f hf V U s :=
  rfl

include hf in
/-- **The comparison is natural in the affine chart `V` of `Y`, as morphisms of sheaves.**  This
is the second half of the assembly: together with
`AlgebraicGeometry.comparisonSheafHom` it says that the comparison is a natural transformation
from `V ↦ g⁻¹h_V` to `V ↦ h_{X ×_Y V}` on the affine étale charts of `Y`. -/
theorem comparisonSheafHom_naturality_chart
    {V' : SmallEtale B Y.obj Y.property}
    [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')] (k : V ⟶ V') :
    g.toToposHom.inverseImage.map
          ((SmallEtale.topology B Y.obj Y.property).yoneda.map k) ≫
        comparisonSheafHom B g f hf V' =
      comparisonSheafHom B g f hf V ≫
        (SmallEtale.topology B X.obj X.property).yoneda.map
          ((smallEtaleBaseChange B f).map k) :=
  Sheaf.hom_ext_sections fun U s => by
    rw [(sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map_comp_apply,
      (sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map_comp_apply,
      comparisonSheafHom_app_apply, comparisonSheafHom_app_apply]
    exact comparisonChartHom_naturality_chart B g f hf V k U s

end SheafHom

end AlgebraicGeometry

end
