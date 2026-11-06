module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSectionsGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjDerivation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRelativeRingedToposHom

/-!
# A derivation of `𝒪_{X_étale}` killing the functions from `Y` is a derivation over `ε⁻¹f⁻¹𝒪_Y`

Let `f : X ⟶ Y` be a morphism of schemes with `X` in a big étale site `B`, and let `D` be a
derivation of `𝒪_{X_étale}` with values in a sheaf of `𝒪_{X_étale}`-modules which annihilates
every function pulled back from an open of `Y`
(`AlgebraicGeometry.SmallEtale.pullbackSection`).  That hypothesis is the one the comparison map
`c''` of Stacks 04CS is built from, and it is weaker on its face than being a derivation over the
inverse-image structure sheaf: the sections of `ε⁻¹f⁻¹𝒪_Y` over an object of the small étale
site need not come from a single section of `𝒪_Y`.

This module proves that it is not weaker: such a `D` annihilates the whole image of the relative
structure map `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRelativeRingedToposHom.lean`,
hence is a derivation over `ε⁻¹f⁻¹𝒪_Y` in the sense of Stacks 04BN.

## Main definitions

* `AlgebraicGeometry.SmallEtale.zariskiStructureMap` is `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` with its type
  recorded for the small Zariski site, the form in which `ε⁻¹` consumes it.
* `AlgebraicGeometry.SmallEtale.relativeDerivation` is `D` read as a derivation over
  `ε⁻¹f⁻¹𝒪_Y`, and `AlgebraicGeometry.SmallEtale.relativeAssociatedDerivation` is `d^a` in that
  form.

## Main results

* `AlgebraicGeometry.SmallEtale.d_relativeStructureMap_eq_zero`: the vanishing itself.
* `AlgebraicGeometry.SmallEtale.d_relativeStructureMap_imageSections_eq_zero`: the special case
  of a section of `f⁻¹𝒪_Y` over the image open of the object, which is the case the local
  surjectivity reduces the general one to.
* `AlgebraicGeometry.SmallEtale.exists_relativeStructureMap_eq_pullbackSection`: conversely every
  function pulled back from an open of `Y` lies in the image of the relative structure map, so
  a derivation over `ε⁻¹f⁻¹𝒪_Y` satisfies the hypothesis of
  `AlgebraicGeometry.SmallEtale.differentialsComparison`.  With the vanishing above the two
  classes of derivations coincide, which is
  `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_relativeAssociatedDerivation`: `(Ω_{X/Y})^a`
  with `d^a` corepresents the derivations of `𝒪_{X_étale}` over `ε⁻¹f⁻¹𝒪_Y`.

## Implementation notes

The proof is the argument of Stacks 0H79 — the one carried out for ringed spaces in
`Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero` — run
on the small étale site, but with the sheaf of constants of the derivation replaced by a local
surjectivity.  Writing the sheaf of constants here would need its sheaf condition on a general
site, while the local surjectivity is already available: `ε⁻¹𝒢` is the étale sheafification of
`(h : V → X) ↦ 𝒢(h(V))`, which is
`AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImageOf`.

So a section of `ε⁻¹f⁻¹𝒪_Y` over `V` is, on an étale covering of `V`, a section of `f⁻¹𝒪_Y`
over an image open `U` of `X`; the relative structure map carries it to the restriction along
`AlgebraicGeometry.SmallEtale.toImageOpen` of the image of that section under `f♯` over `U`,
read on the small étale site, by
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage_comp_inverseImageStructureMap`; and
`D` annihilates that because `AlgebraicGeometry.SmallEtale.zariskiRestriction` is a derivation
of `𝒪_X` over `f⁻¹𝒪_Y` on the small Zariski site, which is exactly where the ringed-space form
of 0H79 has already been applied.  Separatedness of the coefficient sheaf finishes.

An earlier reading of this problem recorded
`AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImage` as the input, but
that statement is about `ε⁻¹𝒪_{X_Zar}` only; the coefficient sheaf wanted here is `f⁻¹𝒪_Y`, and
the generalization in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleImageSectionsGeneral.lean`
is what makes the reduction available.

**What this does not give.**  `Ω_{X_étale/Y_étale}` is the module of differentials of
`f_small^{-1}𝒪_{Y_étale}` for the morphism `f_small : X_étale ⟶ Y_étale` of small étale sites —
not of `ε⁻¹f⁻¹𝒪_Y` — so the universal property proved here is not literally the one 04CS asks
for, and the canonical isomorphism of Stacks 04CS is not registered here.

Identifying the two base sheaves is *not* what 04CS needs, and it is still not done.  What it
needs is the comparison of the two *classes of derivations*, and that is carried out, for
`f_small^{-1}𝒪_{Y_étale}` directly, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean`: the
adjunction `f_small^{-1} ⊣ f_{small,*}` for sheaves of sets turns the vanishing over
`f_small^{-1}𝒪_{Y_étale}` into a vanishing on the sections of
`AlgebraicGeometry.structureSharp`, which are given by a formula.  The canonical isomorphism is
`AlgebraicGeometry.SmallEtale.differentialsIso` there.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site.
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79), whose non-formal step
  is the comparison of the two ways of being a derivation "over `Y`".
* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA), which exhibits `ε⁻¹`
  as the sheafification of the sections over the image opens.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- The structure map `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of a morphism of schemes, with its type recorded as a
morphism of sheaves of commutative rings for `Opens.grothendieckTopology ↥X`.  This is the
spelling `ε⁻¹` consumes, and the one
`AlgebraicGeometry.SmallEtale.relativeStructureMap` is built from. -/
public noncomputable def zariskiStructureMap :
    Scheme.Hom.inverseImageCommRingSheaf f ⟶ X.zariskiCommRingSheaf :=
  AlgebraicGeometry.inverseImageStructureMap f

/-- The relative structure map is `ε⁻¹f♯` followed by the structure map of `ε`. -/
public theorem relativeStructureMap_eq :
    relativeStructureMap B X hX f
      = (inverseImageCommRing B X hX).map (zariskiStructureMap f) ≫
          inverseImageStructureMap B X hX :=
  rfl

/-- The comparison map `(h : V → X) ↦ (f⁻¹𝒪_Y)(h(V))` `⟶` `ε⁻¹f⁻¹𝒪_Y`, through which a section
of `ε⁻¹f⁻¹𝒪_Y` is locally a section of `f⁻¹𝒪_Y` over an image open. -/
public noncomputable abbrev relativeImageSectionsComparison :
    imageSectionsPresheafOf B X hX (Scheme.Hom.inverseImageCommRingSheaf f) ⟶
      (relativeStructureSheaf B X hX f).obj :=
  imageSectionsToInverseImageOf B X hX (Scheme.Hom.inverseImageCommRingSheaf f)

variable {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}
  (D : PresheafOfModulesOfCommRing.Derivation'
    (R := (commRingStructureSheaf B X hX).obj) F.val ψ)

/-- **The relative structure map on a section of `f⁻¹𝒪_Y` over an image open.**  Over an object
`V` of the small étale site, a section of `f⁻¹𝒪_Y` over the image open of `V` is carried by the
relative structure map to the restriction along
`AlgebraicGeometry.SmallEtale.toImageOpen` of its image under `f♯`, read on the small étale
site through the structure map of `ε`. -/
public theorem relativeStructureMap_imageSectionsComparison
    (V : (SmallEtale B X hX)ᵒᵖ)
    (s : (imageSectionsPresheafOf B X hX (Scheme.Hom.inverseImageCommRingSheaf f)).obj V) :
    ((relativeStructureMap B X hX f).hom.app V).hom
        ((relativeImageSectionsComparison B hX f).app V s)
      = (commRingStructureSheaf B X hX).obj.map (toImageOpen B X hX V.unop).op
          (((commRingStructureMap B X hX).hom.app (op (imageOpen B X hX V.unop))).hom
            (((zariskiStructureMap f).hom.app (op (imageOpen B X hX V.unop))).hom s)) := by
  have hnat := imageSectionsToInverseImageOf_app_apply_naturality B X hX
    (zariskiStructureMap f) V s
  have hcomp : ((imageSectionsToInverseImage B X hX).app V ≫
        (inverseImageStructureMap B X hX).hom.app V)
      = (imageSectionsRestriction B X hX).app V :=
    congrArg (fun m : imageSectionsPresheaf B X hX ⟶ (commRingStructureSheaf B X hX).obj =>
      m.app V) (imageSectionsToInverseImage_comp_inverseImageStructureMap B X hX)
  rw [relativeStructureMap_eq]
  refine Eq.trans (ConcreteCategory.comp_apply
    (((inverseImageCommRing B X hX).map (zariskiStructureMap f)).hom.app V)
    ((inverseImageStructureMap B X hX).hom.app V) _) ?_
  rw [← hnat]
  refine Eq.trans (ConcreteCategory.comp_apply ((imageSectionsToInverseImage B X hX).app V)
    ((inverseImageStructureMap B X hX).hom.app V) _).symm ?_
  rw [hcomp]
  rfl

/-- **A derivation annihilating the functions pulled back from `Y` annihilates the sections of
`f⁻¹𝒪_Y` over the image opens.**  This is the vanishing of
`AlgebraicGeometry.SmallEtale.zariskiRestriction` over `f⁻¹𝒪_Y` on the small Zariski site,
carried along the restriction of
`AlgebraicGeometry.SmallEtale.relativeStructureMap_imageSectionsComparison`. -/
public theorem d_relativeStructureMap_imageSections_eq_zero
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (V : (SmallEtale B X hX)ᵒᵖ)
    (s : (imageSectionsPresheafOf B X hX (Scheme.Hom.inverseImageCommRingSheaf f)).obj V) :
    D.d (((relativeStructureMap B X hX f).hom.app V).hom
        ((relativeImageSectionsComparison B hX f).app V s)) = 0 := by
  have hzero : (zariskiRestrictionData B hX D).d
      (((zariskiStructureMap f).hom.app (op (imageOpen B X hX V.unop))).hom s) = 0 :=
    PresheafOfModulesOfCommRing.Derivation'.d_app (zariskiRestriction B hX f D hD) s
  have hd : D.d (X := op ((opensToSmallEtale B X hX).obj (imageOpen B X hX V.unop)))
      (((commRingStructureMap B X hX).hom.app (op (imageOpen B X hX V.unop))).hom
        (((zariskiStructureMap f).hom.app (op (imageOpen B X hX V.unop))).hom s)) = 0 :=
    Eq.trans (zariskiRestrictionData_d B hX D (W := op (imageOpen B X hX V.unop)) _).symm hzero
  rw [relativeStructureMap_imageSectionsComparison B hX f V s]
  refine Eq.trans (D.d_map (toImageOpen B X hX V.unop).op _) ?_
  rw [hd]
  exact map_zero _

/-- **A derivation of `𝒪_{X_étale}` annihilating every function pulled back from an open of `Y`
annihilates the whole image of `ε⁻¹f⁻¹𝒪_Y ⟶ 𝒪_{X_étale}`**, so it is a derivation over
`ε⁻¹f⁻¹𝒪_Y`.

A section of `ε⁻¹f⁻¹𝒪_Y` over `V` is, on an étale covering of `V`, the image of a section of
`f⁻¹𝒪_Y` over an image open; the derivation annihilates those by
`AlgebraicGeometry.SmallEtale.d_relativeStructureMap_imageSections_eq_zero`, and the coefficient
sheaf is separated. -/
public theorem d_relativeStructureMap_eq_zero
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (V : (SmallEtale B X hX)ᵒᵖ) (a : (relativeStructureSheaf B X hX f).obj.obj V) :
    D.d (((relativeStructureMap B X hX f).hom.app V).hom a) = 0 := by
  refine F.isSheaf.isSeparated _ (Presheaf.imageSieve (relativeImageSectionsComparison B hX f) a)
    (Presheaf.imageSieve_mem (topology B X hX) (relativeImageSectionsComparison B hX f) a)
    _ 0 ?_
  rintro W g ⟨c, hc⟩
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans (D.d_map g.op _).symm ?_
  refine Eq.trans (congrArg D.d ?_) (d_relativeStructureMap_imageSections_eq_zero B hX f D hD _ c)
  refine Eq.trans
    (NatTrans.naturality_apply (relativeStructureMap B X hX f).hom g.op a).symm ?_
  exact congrArg (fun t => ((relativeStructureMap B X hX f).hom.app (op W)).hom t) hc.symm

/-- **`D` read as a derivation over `ε⁻¹f⁻¹𝒪_Y`.**  The same values; what is added is the
vanishing condition of Stacks 04BN over the relative structure map, which
`AlgebraicGeometry.SmallEtale.d_relativeStructureMap_eq_zero` supplies. -/
public noncomputable def relativeDerivation
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (relativeStructureMap B X hX f).hom where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {V} a := d_relativeStructureMap_eq_zero B hX f D hD V a

/-- **`d^a` as a derivation of `𝒪_{X_étale}` over `ε⁻¹f⁻¹𝒪_Y`.** -/
public noncomputable def relativeAssociatedDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      (associatedRelativeDifferentials B hX f).val (relativeStructureMap B X hX f).hom :=
  relativeDerivation B hX f (associatedDerivation B hX f)
    (associatedDerivation_pullbackSection_eq_zero B hX f)

/-! ### The converse: the pulled-back functions lie in the image of the relative structure map -/

/-- **The relative structure map over an open of `X`.**  A section of `f⁻¹𝒪_Y` over an open `U`
of `X`, read in `ε⁻¹f⁻¹𝒪_Y` over the object `U` of the small étale site by the unit of the
adjunction `ε⁻¹ ⊣ ε_*`, is carried by the relative structure map to the image of that section
under `f♯`, read on the small étale site through the structure map of `ε`.

Both sides are transposes of `f♯` followed by the structure map of `ε`: the relative structure
map is `ε⁻¹f♯` followed by
`AlgebraicGeometry.SmallEtale.inverseImageStructureMap`, which is by definition the transpose
of `AlgebraicGeometry.SmallEtale.commRingStructureMap`. -/
public theorem relativeStructureMap_app_unit (U : (X.Opens)ᵒᵖ)
    (s : (Scheme.Hom.inverseImageCommRingSheaf f).obj.obj U) :
    ((relativeStructureMap B X hX f).hom.app
          (op ((opensToSmallEtale B X hX).obj U.unop))).hom
        ((((inverseImageCommRingAdjunction B X hX).unit.app
            (Scheme.Hom.inverseImageCommRingSheaf f)).hom.app U).hom s)
      = ((commRingStructureMap B X hX).hom.app U).hom
          (((zariskiStructureMap f).hom.app U).hom s) := by
  have hism : (inverseImageCommRingAdjunction B X hX).homEquiv X.zariskiCommRingSheaf
        (commRingStructureSheaf B X hX) (inverseImageStructureMap B X hX)
      = commRingStructureMap B X hX :=
    Equiv.apply_symm_apply _ _
  have h : (inverseImageCommRingAdjunction B X hX).homEquiv
        (Scheme.Hom.inverseImageCommRingSheaf f) (commRingStructureSheaf B X hX)
        (relativeStructureMap B X hX f)
      = zariskiStructureMap f ≫ commRingStructureMap B X hX := by
    rw [relativeStructureMap_eq, Adjunction.homEquiv_naturality_left, hism]
    rfl
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun m : Scheme.Hom.inverseImageCommRingSheaf f ⟶
      ((opensToSmallEtale B X hX).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology ↥X) (topology B X hX)).obj
        (commRingStructureSheaf B X hX) => (m.hom.app U).hom s) h

/-- **Every function pulled back from an open of `Y` lies in the image of the relative structure
map.**  Over the object `f⁻¹W` of the small étale site, the section
`AlgebraicGeometry.SmallEtale.pullbackSection` is the image of the canonical section of
`f⁻¹𝒪_Y` attached to `b` by the unit of `f⁻¹ ⊣ f_*`, read in `ε⁻¹f⁻¹𝒪_Y` by the unit of
`ε⁻¹ ⊣ ε_*`.

So the hypothesis of `AlgebraicGeometry.SmallEtale.differentialsComparison` holds for every
derivation over `ε⁻¹f⁻¹𝒪_Y`, which with
`AlgebraicGeometry.SmallEtale.d_relativeStructureMap_eq_zero` makes the two classes of
derivations coincide. -/
public theorem exists_relativeStructureMap_eq_pullbackSection (W : Y.Opens) (b : Γ(Y, W)) :
    ∃ a : (relativeStructureSheaf B X hX f).obj.obj
      (op ((opensToSmallEtale B X hX).obj (f ⁻¹ᵁ W))),
      ((relativeStructureMap B X hX f).hom.app
          (op ((opensToSmallEtale B X hX).obj (f ⁻¹ᵁ W)))).hom a
        = pullbackSection B hX f W b := by
  have hzar : ((zariskiStructureMap f).hom.app (op (f ⁻¹ᵁ W))).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
            Y.sheaf).hom.app (op W)).hom b)
      = (f.app W).hom b := by
    have h := Scheme.Hom.homEquiv_inverseImageStructureMap f
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg (fun m : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf =>
      (m.hom.app (op W)).hom b) h
  refine ⟨(((inverseImageCommRingAdjunction B X hX).unit.app
      (Scheme.Hom.inverseImageCommRingSheaf f)).hom.app (op (f ⁻¹ᵁ W))).hom
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      Y.sheaf).hom.app (op W)).hom b), ?_⟩
  refine Eq.trans (relativeStructureMap_app_unit B hX f (op (f ⁻¹ᵁ W)) _) ?_
  exact congrArg (fun t => ((commRingStructureMap B X hX).hom.app (op (f ⁻¹ᵁ W))).hom t) hzar

/-- A derivation of `𝒪_{X_étale}` over `ε⁻¹f⁻¹𝒪_Y`, read as a derivation over the constant
presheaf of rings `ℤ`: the same values, with only the Leibniz rule recorded. -/
public noncomputable def ofRelativeDerivation
    (E : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (relativeStructureMap B X hX f).hom) :
    PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (siteConstIntMap B hX _) where
  d := E.d
  d_mul := E.d_mul
  d_map := E.d_map
  d_app {V} a :=
    siteConstIntMap_app_eq_zero (P := (commRingStructureSheaf B X hX).obj) B hX E.d (E.d_one V) a

/-- A derivation of `𝒪_{X_étale}` over `ε⁻¹f⁻¹𝒪_Y` annihilates every function pulled back from
an open of `Y`, those lying in the image of the relative structure map. -/
public theorem ofRelativeDerivation_pullbackSection_eq_zero
    (E : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (relativeStructureMap B X hX f).hom) (W : Y.Opens) (b : Γ(Y, W)) :
    (ofRelativeDerivation B hX f E).d (pullbackSection B hX f W b) = 0 := by
  obtain ⟨a, ha⟩ := exists_relativeStructureMap_eq_pullbackSection B hX f W b
  exact Eq.trans (congrArg E.d ha.symm) (PresheafOfModulesOfCommRing.Derivation'.d_app E a)

/-! ### The universal property of `d^a` among the derivations over `ε⁻¹f⁻¹𝒪_Y` -/

section Universal

variable {G : SheafOfModules.{u} (structureSheaf B X hX)}

/-- **`(Ω_{X/Y})^a` with `d^a` corepresents the derivations of `𝒪_{X_étale}` over
`ε⁻¹f⁻¹𝒪_Y`.**

This is `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` with its
hypothesis replaced by the vanishing condition of Stacks 04BN over the relative structure map.
The two are interchangeable: the vanishing over `ε⁻¹f⁻¹𝒪_Y` implies the vanishing on the
functions pulled back from an open of `Y` because those lie in the image of the relative
structure map
(`AlgebraicGeometry.SmallEtale.exists_relativeStructureMap_eq_pullbackSection`), and conversely
by `AlgebraicGeometry.SmallEtale.d_relativeStructureMap_eq_zero`.  A derivation is determined by
its values, so the two factorization conditions are the same condition. -/
public theorem existsUnique_postcomp_relativeAssociatedDerivation
    (E : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) G.val
      (relativeStructureMap B X hX f).hom) :
    ∃! g : associatedRelativeDifferentials B hX f ⟶ G,
      (relativeAssociatedDerivation B hX f).postcomp g.val = E := by
  have key : ∀ g : associatedRelativeDifferentials B hX f ⟶ G,
      ((relativeAssociatedDerivation B hX f).postcomp g.val = E ↔
        (associatedDerivation B hX f).postcomp g.val = ofRelativeDerivation B hX f E) := by
    refine fun g => ⟨fun h => ?_, fun h => ?_⟩ <;>
      exact PresheafOfModulesOfCommRing.Derivation.ext (funext fun V => AddMonoidHom.ext fun a =>
        PresheafOfModulesOfCommRing.Derivation.congr_d h a)
  obtain ⟨g, hg, hu⟩ := existsUnique_postcomp_associatedDerivation B hX f
    (ofRelativeDerivation B hX f E) (ofRelativeDerivation_pullbackSection_eq_zero B hX f E)
  exact ⟨g, (key g).2 hg, fun g' hg' => hu g' ((key g').1 hg')⟩

end Universal

end AlgebraicGeometry.SmallEtale

end
