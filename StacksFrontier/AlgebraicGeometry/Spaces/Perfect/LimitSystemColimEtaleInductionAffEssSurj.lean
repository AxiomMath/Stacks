module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffinePointSpace

/-!
# The induction of Stacks 08GP for essential surjectivity in Stacks 09RJ, with its affine case

In Situation 09RH the essential-surjectivity half of Stacks 09RJ says that every perfect object
of `D(𝒪_X)` is the derived pullback of a perfect object of some `D(𝒪_{X_i})`.  The source proves
it by the induction principle of Stacks 08GP over the quasi-compact quasi-separated objects
`U₀` of `(X₀)_{spaces, étale}`, the predicate being the same statement for the base-changed
system `U_i = X_i ×_{X₀} U₀` with limit `U = X ×_{X₀} U₀`.

**This file runs that induction in the `smallEtale` spelling of the derived pullback and closes
its affine base case.**  The affine case is proved as
`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affinePointStage` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/`
`LimitPerfectEssentialSurjectivityAffinePointSpace.lean`, but only for the base change along an
*affine point* `u : h_U ⟶ X₀` — a morphism whose source is the presheaf represented by an object
of the big fppf site with affine underlying scheme.  The base case of Stacks 08GP is the
statement at an affine *algebraic space* `V` étale over `X₀`, which is isomorphic to such a
presheaf but is not one.  Transporting across that isomorphism is what this file does, and it is
the whole of the affine clause `haff` of
`AlgebraicGeometry.Space.qcqs_induction_on_self`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.SmallEtalePerfectObjectsDescend`: the conclusion of
  the essential-surjectivity half of Stacks 09RJ for a situation, written with
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` along the projections.
* `AlgebraicGeometry.Space.DescentSituation.SmallEtaleRestrictedObjectsDescend`: **the predicate
  of the induction** — that conclusion for the base change of Situation 09RH along
  `u : U₀ ⟶ X₀`, for every structure of a quasi-compact quasi-separated algebraic space on `U₀`,
  so that it is a property of `u` alone.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.SmallEtalePerfectObjectsDescend.of_stageIso`: the
  conclusion transports along isomorphisms of the stages and of the limit that commute with the
  projections.  The three steps are the composition law of Stacks 0D6D, the invariance of
  perfectness under derived pullback (Stacks 08H6) and the cancellation
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackHomInvIso`.
* `AlgebraicGeometry.Space.DescentSituation.smallEtaleRestrictedObjectsDescend_of_isAffineSpace`:
  **the affine base case of the induction, discharged** — the predicate at an affine algebraic
  space over the chosen stage.
* `AlgebraicGeometry.Space.DescentSituation.smallEtalePerfectObjectsDescend_of_edsStep`:
  **the induction of Stacks 08GP, run**, with the affine clause discharged and the
  elementary-distinguished-square clause as its hypothesis `hstep`.

## The hypotheses carried

*`I : Type u` and `hI : #I < B.cutoff.ord.cof`.*  Both come from the affine case and from nothing
else below; they are the two universe restrictions of Stacks 09RI and 09RJ.  `hI` is the size
bound of Stacks 07SF, which enters the affine case twice — through
`AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π`, the affineness of
`X ×_{X₀} U`, and through `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`,
the colimit of rings of Stacks 07SI.  Neither is removable in the big fppf sites of this library:
`AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineStageLargeIndexCounterexample.lean` and
`AlgebraicGeometry.Space.Refute07SI.not_forall_isSectionsColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitLargeIndexCounterexample.lean` refute
the unbounded statements.  `I : Type u` is forced by
`AlgebraicGeometry.Space.DescentSituation.toLimitSituation`, through which Stacks 07SI for the
structure sheaf is proved.

*`hstep`, the step of the induction across an elementary distinguished square.*  This is a
hypothesis and not a conclusion.  The step itself is proved, unconditionally, as
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectSquareStep.lean`; what is missing
between that and the clause below is the identification of the members of the square base changed
to a stage with the base changes of the members — the fibre-product description that
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjInterSystem.lean` records as
deliberately not assumed there — together with the comparison isomorphism over the intersection,
which the source takes from Stacks 09RI.  No `Prop` binder below stands in for anything else.

No `@[stacks 09RJ]` attribute is placed here.  The essential-surjectivity half of the tag is
already proved in the `spacesEtaleModel` spelling, as
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_chartsBounded` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/RestrictedPerfectDescentOverIntegers.lean`, and
carries the tag there; the statements below are the same mathematics in the spelling the
dévissage of Stacks 09RI runs on, and the one of them that is a reduction is conditional.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 70.5.1 (Tag 07SF)](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Lemma 75.14.2 (Tag 08H6)](https://stacks.math.columbia.edu/tag/08H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Two isomorphisms of fibre products of presheaves -/

/-- **Precomposing the second leg of a fibre product with an isomorphism.**  For `e : T ≅ T'` the
fibre product of `f` with `u : T ⟶ Y` is the fibre product of `f` with `e.inv ≫ u`.

This is the comparison the affine base case of Stacks 08GP needs: the base change of
Situation 09RH along an affine algebraic space `V` and along the presheaf `h_A` it is isomorphic
to are the two sides. -/
def pullbackIsoPrecompInv {X Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (u : T ⟶ Y)
    (e : T ≅ T') : pullback f u ≅ pullback f (e.inv ≫ u) where
  hom := pullback.lift (pullback.fst f u) (pullback.snd f u ≫ e.hom) (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.condition)
  inv := pullback.lift (pullback.fst f (e.inv ≫ u)) (pullback.snd f (e.inv ≫ u) ≫ e.inv) (by
    rw [Category.assoc]
    exact pullback.condition)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The forward map of `pullbackIsoPrecompInv f u e` commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem pullbackIsoPrecompInv_hom_comp_fst {X Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (u : T ⟶ Y) (e : T ≅ T') :
    (pullbackIsoPrecompInv f u e).hom ≫ pullback.fst f (e.inv ≫ u) = pullback.fst f u :=
  pullback.lift_fst _ _ _

/-- The forward map of `pullbackIsoPrecompInv f u e` followed by the second projection is the
second projection followed by `e.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackIsoPrecompInv_hom_comp_snd {X Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (u : T ⟶ Y) (e : T ≅ T') :
    (pullbackIsoPrecompInv f u e).hom ≫ pullback.snd f (e.inv ≫ u) = pullback.snd f u ≫ e.hom :=
  pullback.lift_snd _ _ _

/-- **The fibre product with an identity is the source.**  This is the comparison that reads the
base change of Situation 09RH along the identity of the chosen stage as the situation itself. -/
def pullbackIdRightIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    pullback f (𝟙 Y) ≅ X where
  hom := pullback.fst f (𝟙 Y)
  inv := pullback.lift (𝟙 X) f (by rw [Category.id_comp, Category.comp_id])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
        Category.id_comp, pullback.condition]
  inv_hom_id := pullback.lift_fst _ _ _

/-- The inverse of `pullbackIdRightIso f` followed by the first projection is the identity. -/
@[reassoc (attr := simp)]
theorem pullbackIdRightIso_inv_comp_fst {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (pullbackIdRightIso f).inv ≫ pullback.fst f (𝟙 Y) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The inverse of `pullbackIdRightIso f` followed by the second projection is `f`. -/
@[reassoc (attr := simp)]
theorem pullbackIdRightIso_inv_comp_snd {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (pullbackIdRightIso f).inv ≫ pullback.snd f (𝟙 Y) = f :=
  pullback.lift_snd _ _ _

/-- **The projections of a base-changed system commute with
`AlgebraicGeometry.Space.pullbackIsoPrecompInv`.**  This is the square the affine base case of
Stacks 08GP consumes: at the level of presheaves it says that base changing along `u` and along
`e.inv ≫ u` give the same system, compatibly with the maps induced by a morphism over the
base. -/
theorem baseChangeOverMap_comp_pullbackIsoPrecompInv_hom
    {X X' Y T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y) (p' : X' ⟶ Y) (a : X ⟶ X')
    (hcomm : a ≫ p' = p) (u : T ⟶ Y) (e : T ≅ T') :
    baseChangeOverMap B S hS p p' a hcomm u ≫ (pullbackIsoPrecompInv p' u e).hom =
      (pullbackIsoPrecompInv p u e).hom ≫
        baseChangeOverMap B S hS p p' a hcomm (e.inv ≫ u) := by
  ext <;> simp

/-- **The projections of the base change along an identity are the original ones.**  This is the
square that reads the base change of Situation 09RH along the identity of the chosen stage as the
situation itself. -/
theorem comp_pullbackIdRightIso_inv {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (a : X ⟶ X') (hcomm : a ≫ p' = p) :
    a ≫ (pullbackIdRightIso p').inv =
      (pullbackIdRightIso p).inv ≫ baseChangeOverMap B S hS p p' a hcomm (𝟙 Y) := by
  ext <;> simp [hcomm]

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})}

/-! ### The conclusion of the essential-surjectivity half of Stacks 09RJ -/

section Conclusion

variable {K : Type u} [Preorder K] [IsDirected K (· ≤ ·)]

/-- **The essential-surjectivity half of Stacks 09RJ for a situation**, written with the derived
pullback `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` along the projections of the
situation: every perfect object of `D(𝒪_X)` is the derived pullback of a perfect object of some
`D(𝒪_{X_i})`.

This is the spelling of
`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affinePointStage` and of the dévissage
of Stacks 09RI, not the `spacesEtaleModel` spelling of
`AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescend`. -/
def SmallEtalePerfectObjectsDescend (A : DescentSituation B S hS hZ K) : Prop :=
  ∀ (E : DerivedCategory (Modules.{u, u} B S hS A.limitSpace.obj A.limitSpace.property)),
    (smallEtaleRingedSite B S hS A.limitSpace.obj A.limitSpace.property).IsPerfect E →
      ∃ (j : K) (Ej : DerivedCategory (Modules.{u, u} B S hS (A.stage j).obj
          (A.stage j).property)),
        (smallEtaleRingedSite B S hS (A.stage j).obj (A.stage j).property).IsPerfect Ej ∧
          Nonempty ((smallEtaleDerivedModulePullback B S hS (A.projection j)).obj Ej ≅ E)

/-- **The conclusion of the essential-surjectivity half of Stacks 09RJ transports along
isomorphisms of the stages and of the limit that commute with the projections.**

Given `E` on the limit of `A`, pull it back along `εL.inv` to the limit of `A'`, descend it there
to a stage `j`, and push the result forward along `εS j`.  The isomorphism required of
`L(f_j)^*` of that object is the composition law of Stacks 0D6D applied around the commuting
square `f_j ≫ εS j = εL ≫ f'_j` and then the cancellation of `Lε_L^*` against `Lε_L^{-1*}`;
perfectness is preserved by derived pullback, which is Stacks 08H6. -/
theorem SmallEtalePerfectObjectsDescend.of_stageIso {A A' : DescentSituation B S hS hZ K}
    (εS : ∀ j : K, A.stage j ≅ A'.stage j) (εL : A.limitSpace ≅ A'.limitSpace)
    (hsq : ∀ j : K, A.projection j ≫ (εS j).hom = εL.hom ≫ A'.projection j)
    (h : A'.SmallEtalePerfectObjectsDescend) : A.SmallEtalePerfectObjectsDescend := by
  intro E hE
  obtain ⟨j, Ej, hEj, ⟨ι⟩⟩ := h ((smallEtaleDerivedModulePullback B S hS εL.inv).obj E)
    (isPerfect_smallEtaleDerivedModulePullback εL.inv E hE)
  refine ⟨j, (smallEtaleDerivedModulePullback B S hS (εS j).hom).obj Ej,
    isPerfect_smallEtaleDerivedModulePullback (εS j).hom Ej hEj, ⟨?_⟩⟩
  exact (smallEtaleDerivedModulePullbackCompIso B S hS (A.projection j) (εS j).hom).app Ej ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS (hsq j)).app Ej ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS εL.hom (A'.projection j)).symm.app Ej ≪≫
        (smallEtaleDerivedModulePullback B S hS εL.hom).mapIso ι ≪≫
          (smallEtaleDerivedModulePullbackHomInvIso B S hS εL).app E

end Conclusion

/-! ### The predicate of the induction and its affine case -/

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The predicate of the induction of Stacks 08GP for essential surjectivity in
Stacks 09RJ.**  For a morphism `u : U₀ ⟶ X₀` onto the chosen stage, the conclusion of the
essential-surjectivity half of the tag for Situation 09RH restricted to its stages and base
changed along `u` — the system `U_i = X_i ×_{X₀} U₀` with limit `U = X ×_{X₀} U₀`.

The structure of a quasi-compact quasi-separated algebraic space on `U₀` is quantified over
rather than assumed, so that this is a property of `u` alone, which is the shape
`AlgebraicGeometry.Space.qcqs_induction_on_self` takes. -/
def SmallEtaleRestrictedObjectsDescend {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (u : U₀ ⟶ (stagesSystem D).obj (op (baseStage D))) : Prop :=
  ∀ (hU₀ : IsAlgebraicSpace B S hS U₀) (hU₀qc : IsQuasiCompactSpace B S hS U₀)
    (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀),
    (D.stagesBaseChangeAlong hU₀ hU₀qc hU₀qs u).SmallEtalePerfectObjectsDescend

variable (hI : #I < B.cutoff.ord.cof)

include hI in
/-- **The affine base case of the induction of Stacks 08GP for essential surjectivity in
Stacks 09RJ**: the predicate holds at every morphism onto the chosen stage whose source is an
affine algebraic space.

`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affinePointStage` is this statement
for the base change along an affine *point* `h_A ⟶ X₀`, the source being the presheaf
represented by an object of the big fppf site with affine underlying scheme.  An affine algebraic
space `U₀` is isomorphic to such a presheaf but is not one, and the chosen isomorphism
`e : U₀ ≅ h_A` carries the base change along `u` to the base change along `e.inv ≫ u` stage by
stage and at the limit, compatibly with the projections: that is
`AlgebraicGeometry.Space.pullbackIsoPrecompInv`, and the conclusion transports across it by
`AlgebraicGeometry.Space.DescentSituation.SmallEtalePerfectObjectsDescend.of_stageIso`.

This is the whole of the clause `haff` of `AlgebraicGeometry.Space.qcqs_induction_on_self` for
this predicate. -/
theorem smallEtaleRestrictedObjectsDescend_of_isAffineSpace
    {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀aff : IsAffineSpace B S hS U₀)
    (u : U₀ ⟶ (stagesSystem D).obj (op (baseStage D))) :
    D.SmallEtaleRestrictedObjectsDescend u := by
  intro hU₀ hU₀qc hU₀qs
  obtain ⟨A, hA, ⟨e⟩⟩ := hU₀aff
  exact SmallEtalePerfectObjectsDescend.of_stageIso
    (A' := affinePointSituation D hA (e.inv ≫ u))
    (fun j => ObjectProperty.isoMk _
      (pullbackIsoPrecompInv ((stagesToBase D).app (op j)) u e))
    (ObjectProperty.isoMk _
      (pullbackIsoPrecompInv ((stagesCone D).π.app (op (baseStage D))) u e))
    (fun j => ObjectProperty.hom_ext _
      (baseChangeOverMap_comp_pullbackIsoPrecompInv_hom
        ((stagesCone D).π.app (op (baseStage D))) ((stagesToBase D).app (op j))
        ((stagesCone D).π.app (op j)) (stagesCone_π_comp D (op j)) u e))
    (fun E hE => exists_isPerfect_affinePointStage hA (e.inv ≫ u) hI E hE)

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
include hI in
/-- **The induction of Stacks 08GP for essential surjectivity in Stacks 09RJ, run.**  In
Situation 09RH, perfect objects on the limit `X` descend to a stage as soon as the predicate
`AlgebraicGeometry.Space.DescentSituation.SmallEtaleRestrictedObjectsDescend` passes across every
elementary distinguished square `(U ⊆ W, V ⟶ W)` of quasi-compact quasi-separated objects of
`(X₀)_{spaces, étale}` with affine `V`.

The affine clause of the induction is
`AlgebraicGeometry.Space.DescentSituation.smallEtaleRestrictedObjectsDescend_of_isAffineSpace`,
and the last step reads the base change along the identity of the chosen stage as the situation
itself, by `AlgebraicGeometry.Space.pullbackIdRightIso`.

`hstep` is stated in exactly the shape `AlgebraicGeometry.Space.qcqs_induction_on_self` asks for;
it is a hypothesis here, and see "The hypotheses carried" in this file's module documentation for
what stands between it and the proved square step of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectSquareStep.lean`. -/
theorem smallEtalePerfectObjectsDescend_of_edsStep
    (hstep : ∀ (W V : SpacesEtale B S hS
        ⟨(stagesSystem D).obj (op (baseStage D)), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      D.SmallEtaleRestrictedObjectsDescend (U.ι ≫ W.1.hom.hom) →
      D.SmallEtaleRestrictedObjectsDescend V.1.hom.hom →
      D.SmallEtaleRestrictedObjectsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.SmallEtaleRestrictedObjectsDescend W.1.hom.hom) :
    (stagesSituation D).SmallEtalePerfectObjectsDescend := by
  have key := qcqs_induction_on_self B S hS hZ
    ⟨(stagesSystem D).obj (op (baseStage D)), D.algebraicSpace D.base⟩
    (D.quasiCompact D.base) (D.quasiSeparated D.base)
    (fun _ y => D.SmallEtaleRestrictedObjectsDescend y)
    (fun V hV => D.smallEtaleRestrictedObjectsDescend_of_isAffineSpace hI hV _) hstep
  exact SmallEtalePerfectObjectsDescend.of_stageIso
    (A' := D.stagesBaseChangeAlong (D.algebraicSpace D.base) (D.quasiCompact D.base)
      (D.quasiSeparated D.base) (𝟙 _))
    (fun j => ObjectProperty.isoMk _ (pullbackIdRightIso ((stagesToBase D).app (op j))).symm)
    (ObjectProperty.isoMk _
      (pullbackIdRightIso ((stagesCone D).π.app (op (baseStage D)))).symm)
    (fun j => ObjectProperty.hom_ext _
      (comp_pullbackIdRightIso_inv ((stagesCone D).π.app (op (baseStage D)))
        ((stagesToBase D).app (op j)) ((stagesCone D).π.app (op j))
        (stagesCone_π_comp D (op j))))
    (key (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base))

end DescentSituation

end AlgebraicGeometry.Space

end
