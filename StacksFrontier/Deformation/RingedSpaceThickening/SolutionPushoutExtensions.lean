module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionBaseRestriction
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor

/-!
# The two pushout extensions of the torsor of solutions of Stacks 08UC

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening with ideal `𝒥`, `f : X ⟶ S` a
morphism of ringed spaces, `𝒢` an `𝒪_X`-module and `c : f^* t^* 𝒥 ⟶ 𝒢`. The proof of
**Stacks 08UC** makes the solutions of the lifting problem of **Stacks 08U7** into a torsor
under `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` by two square-zero pushout constructions, which this file
supplies, reading a solution `Q` as the square-zero extension `Q.toAlgebraExtension` of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionAlgebraExtensionBridge.lean`.

* **The difference of two solutions.** For two solutions `Q₁`, `Q₂` the Baer difference of
  their extensions is the square-zero pushout of the common refinement
  `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}` along the difference of the two maps on ideals. Both extensions
  induce the same map `c` on `t^*𝒥`, so the difference kills `Ker(t^♯)` and the pushout is an
  extension of `f⁻¹𝒪_S`-algebras: an element of `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`. Read back over
  `S'` it has the class `[Q₁] - [Q₂]`.
* **Adding a class to a solution.** For a solution `Q` and an extension `𝒪_{X''}` of
  `f⁻¹𝒪_S`-algebras, the Baer sum of `Q.toAlgebraExtension` with `𝒪_{X''}` read over `S'`
  induces `c + 0 = c` on `t^*𝒥`, so it is again the extension of a solution, of class
  `[Q] + [𝒪_{X''}]`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.coefficientSection`: the image of a section of the
  base in the polynomial algebra of a presentation.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.differenceExtension`: the
  difference extension of two solutions, an extension of `f⁻¹𝒪_S`-algebras.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extensionOfConormalHom_ideal_adjointBase`: the
  algebra structure of the square-zero pushout along `δ` carries a section of the base killed by
  the structure map to the value of `δ` at its coefficient section.
* `DeformationSolution.restrictBase_differenceExtension_extClass`: the class of the difference
  extension, read over `S'`, is `[Q₁] - [Q₂]`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.exists_extClass_eq_add`: for a
  solution `Q` and an extension `𝒪_{X''}` of `f⁻¹𝒪_S`-algebras there is a solution of class
  `[Q] + [𝒪_{X''}]`.

## Implementation notes

No `@[stacks]` attribute is attached: these are the two constructions inside the proof of
**Stacks 08UC**, not its statement.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.Conormal (IdealRestriction conormalSheaf conormalDesc
  conormalDesc_toAssociatedModule kernelIdeal)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafDesc freeAlgebraSheafCoefficientMap_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The coefficient section of a section of the base -/

section Coefficient

variable {X T : RingedSpace.{u, u}} {g : X ⟶ T}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}

variable (g E) in
/-- The adjoint `𝒪_T ⟶ g_* (g⁻¹𝒪_T[ℰ])` of the inclusion of the coefficients into the
polynomial algebra of a presentation. -/
abbrev coefficientAdjoint :
    T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing g) E) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing g) E)

variable (g E) in
/-- **The coefficient section of a section `s` of `𝒪_T`**: its image in the polynomial algebra
`g⁻¹𝒪_T[ℰ]`, over the preimage of the open of `s`. -/
abbrev coefficientSection (V : (Opens T.carrier)ᵒᵖ) (s : T.presheaf.obj V) :
    ↥((freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing g) E).obj.obj
      (op ((Opens.map g.hom.base).obj V.unop))) :=
  ((coefficientAdjoint g E).hom.app V).hom s

/-- The adjoint of a map `b` out of the coefficients that factors as the coefficient map followed
by `φ` is, at a section `s`, `φ` at the coefficient section of `s`. -/
private theorem homEquiv_app_eq_of_coefficientMap_comp
    {H : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (φ : freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing g) E ⟶ H)
    (b : inverseImageBaseRing g ⟶ H)
    (hb : freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing g) E ≫ φ = b) (V : (Opens T.carrier)ᵒᵖ) (s : T.presheaf.obj V) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
        b).hom.app V).hom s) = (φ.hom.app _).hom (coefficientSection g E V s) := by
  subst hb
  have h : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing g) E ≫ φ) = coefficientAdjoint g E ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map φ :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      g.hom.base).homEquiv_naturality_right _ _
  exact congrArg (fun k => (k.hom.app V).hom s) h

/-- The coefficient section of a section of the base killed by the comorphism is a local
relation of the presentation. -/
theorem coefficientSection_mem_kernelIdeal (V : (Opens T.carrier)ᵒᵖ) (s : T.presheaf.obj V)
    (hs : (g.hom.c.app V).hom s = 0) :
    coefficientSection g E V s ∈
      kernelIdeal (generatorsPresentation g E α).hom (op ((Opens.map g.hom.base).obj V.unop)) := by
  have h := homEquiv_app_eq_of_coefficientMap_comp (generatorsPresentation g E α)
    (structureRingMap g)
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing g) X.sheaf E (structureRingMap g) α) V s
  have e : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      g.hom.base).homEquiv _ _ (structureRingMap g) = ObjectProperty.homMk g.hom.c :=
    Equiv.apply_symm_apply _ _
  rw [e] at h
  exact h.symm.trans hs

/-- The adjoint of the algebra structure of a presented extension, at a section `s` of the
base, is the lift of the presentation at the coefficient section of `s`. -/
theorem PresentedSquareZeroExtension.adjoint_base_app (P : PresentedSquareZeroExtension g G E α)
    (V : (Opens T.carrier)ᵒᵖ) (s : T.presheaf.obj V) :
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
        P.base).hom.app V).hom s) = (P.lift.hom.app _).hom (coefficientSection g E V s) :=
  homEquiv_app_eq_of_coefficientMap_comp P.lift P.base
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing g) P.sheaf E P.base P.liftGen) V s

/-- **The restriction datum of a presented extension at the coefficient section of `s`** is the
identification of the ideal at the image of `s` under the algebra structure. -/
theorem PresentedSquareZeroExtension.idealRestriction_app_coefficientSection
    (P : PresentedSquareZeroExtension g G E α) (V : (Opens T.carrier)ᵒᵖ) (s : T.presheaf.obj V)
    (hk : coefficientSection g E V s ∈
      kernelIdeal (generatorsPresentation g E α).hom (op ((Opens.map g.hom.base).obj V.unop)))
    (hm : ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
        P.base).hom.app V).hom s) ∈
      kernelIdeal P.reduction.hom (op ((Opens.map g.hom.base).obj V.unop))) :
    P.idealRestriction.app _ ⟨coefficientSection g E V s, hk⟩ =
      P.ideal.app _ ⟨((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        g.hom.base).homEquiv _ _ P.base).hom.app V).hom s), hm⟩ :=
  congrArg (P.ideal.app _) (Subtype.ext (P.adjoint_base_app V s).symm)

/-- The ideal restriction attached to the descent of a restriction datum through the conormal
sheaf is that restriction datum. -/
theorem conormalRestriction_conormalDesc_app
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation g E α).hom]
    (ρ : IdealRestriction.{u, u, u, u} (generatorsPresentation g E α) G)
    (U : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal (generatorsPresentation g E α).hom U)) :
    (Stacks.Sites.Conormal.conormalRestriction.{u, u, u} (Opens.grothendieckTopology X.carrier)
        (generatorsPresentation g E α) G
        (conormalDesc.{u, u, u, u} (generatorsPresentation g E α) G ρ)).app U y = ρ.app U y :=
  conormalDesc_toAssociatedModule.{u, u, u, u} (generatorsPresentation g E α) G ρ U y

variable [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation g E α).hom]
  (δ : conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing g) E)
      X.sheaf (generatorsPresentation g E α) ⟶ G)

/-- **The algebra structure of the square-zero pushout along `δ`, at a section of the base
killed by the comorphism, is `δ` at the coefficient section.** The algebra structure is the
inclusion of the coefficients followed by the inclusion of the polynomial algebra into the
pushout, and that inclusion carries a local relation to the image of its value under `δ`. -/
theorem extensionOfConormalHom_ideal_adjointBase (V : (Opens T.carrier)ᵒᵖ)
    (s : T.presheaf.obj V)
    (hk : coefficientSection g E V s ∈
      kernelIdeal (generatorsPresentation g E α).hom (op ((Opens.map g.hom.base).obj V.unop)))
    (hm : (((extensionOfConormalHom δ).adjointBase.hom.app V).hom s) ∈
      kernelIdeal (extensionOfConormalHom δ).reduction.hom
        (op ((Opens.map g.hom.base).obj V.unop))) :
    (extensionOfConormalHom δ).ideal.app _
        ⟨((extensionOfConormalHom δ).adjointBase.hom.app V).hom s, hm⟩ =
      (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
        (Opens.grothendieckTopology X.carrier) (generatorsPresentation g E α) G δ).app _
        ⟨coefficientSection g E V s, hk⟩ := by
  have hval : ((extensionOfConormalHom δ).adjointBase.hom.app V).hom s =
      ((pushoutLift δ).hom.app _).hom (coefficientSection g E V s) :=
    homEquiv_app_eq_of_coefficientMap_comp _ _ rfl V s
  exact idealRestriction_app_eq_of_val.{u} (generatorsPresentation g E α) G
    (conormalPushoutData δ) _ _ _
    (hval.trans (pushoutInl_app_kernel.{u} (generatorsPresentation g E α)
      (restrictAlong.{u} (generatorsPresentation g E α) G) (conormalPushoutData δ) _
      ⟨coefficientSection g E V s, hk⟩))

end Coefficient

/-! ### The two pushout extensions of solutions -/

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-- A section of `𝒪_{S'}` killed by `t^♯` is killed by the comorphism of `f ∘ t`. -/
theorem comp_c_app_eq_zero (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) : ((f ≫ t).hom.c.app V).hom s = 0 := by
  change (f.hom.c.app _).hom ((t.hom.c.app V).hom s) = 0
  rw [hs, map_zero]

/-- **The restriction datum of the first extension of a pair, at the coefficient section of a
section of `Ker(t^♯)`, is the prescribed map `c`.** -/
theorem pairRefinementFst_idealRestriction_coefficientSection
    (Q₁ : DeformationSolution t ht f G c) (P₂ : AlgebraSquareZeroExtension (f ≫ t) G)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : coefficientSection (f ≫ t) (pairRefinementGenerators Q₁.toAlgebraExtension P₂) V s ∈
      kernelIdeal (generatorsPresentation (f ≫ t) _
        (pairRefinementMap Q₁.toAlgebraExtension P₂)).hom
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))) :
    (pairRefinementFst Q₁.toAlgebraExtension P₂).idealRestriction.app _
        ⟨coefficientSection (f ≫ t) _ V s, hk⟩ = prescribedIdealSection c V s hs :=
  ((pairRefinementFst Q₁.toAlgebraExtension P₂).idealRestriction_app_coefficientSection V s hk
    (Q₁.toAlgebraExtension.adjointBase_mem_kernelIdeal V s hs)).trans
    (Q₁.toAlgebraExtension_ideal_adjointBase V s hs)

/-- **The restriction datum of the second extension of a pair, at the coefficient section of a
section of `Ker(t^♯)`, is the prescribed map `c`.** -/
theorem pairRefinementSnd_idealRestriction_coefficientSection
    (P₁ : AlgebraSquareZeroExtension (f ≫ t) G) (Q₂ : DeformationSolution t ht f G c)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hk : coefficientSection (f ≫ t) (pairRefinementGenerators P₁ Q₂.toAlgebraExtension) V s ∈
      kernelIdeal (generatorsPresentation (f ≫ t) _
        (pairRefinementMap P₁ Q₂.toAlgebraExtension)).hom
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop))) :
    (pairRefinementSnd P₁ Q₂.toAlgebraExtension).idealRestriction.app _
        ⟨coefficientSection (f ≫ t) _ V s, hk⟩ = prescribedIdealSection c V s hs :=
  ((pairRefinementSnd P₁ Q₂.toAlgebraExtension).idealRestriction_app_coefficientSection V s hk
    (Q₂.toAlgebraExtension.adjointBase_mem_kernelIdeal V s hs)).trans
    (Q₂.toAlgebraExtension_ideal_adjointBase V s hs)

/-- The difference homomorphism `𝒥/𝒥² ⟶ 𝒢` of the extensions of two solutions, over the
common refinement `𝒪_{X'₁} ×_{𝒪_X} 𝒪_{X'₂}`. -/
abbrev differenceHom (Q₁ Q₂ : DeformationSolution t ht f G c) :=
  PresentedSquareZeroExtension.obstruction (pairRefinementFst Q₁.toAlgebraExtension
    Q₂.toAlgebraExtension) (pairRefinementSnd Q₁.toAlgebraExtension Q₂.toAlgebraExtension)

/-- The Baer difference of the extensions of two solutions, as an extension of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras: the square-zero pushout of the common refinement along the
difference homomorphism. -/
abbrev differencePushout (Q₁ Q₂ : DeformationSolution t ht f G c) :
    AlgebraSquareZeroExtension (f ≫ t) G :=
  extensionOfConormalHom (Q₁.differenceHom Q₂)

/-- **The algebra structure of the Baer difference of two solutions kills `Ker(t^♯)`.** At a
section `s` of `Ker(t^♯)` it is the difference of the values of the two solutions, which are
both the prescribed value `c(s)`. -/
theorem differencePushout_adjointBase_eq_zero (Q₁ Q₂ : DeformationSolution t ht f G c)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    ((adjointBaseHom f (Q₁.differencePushout Q₂).sheaf
      (Q₁.differencePushout Q₂).base).hom.app V).hom s = 0 := by
  have hm := (Q₁.differencePushout Q₂).adjointBase_mem_kernelIdeal V s hs
  have hk := coefficientSection_mem_kernelIdeal (g := f ≫ t)
    (E := pairRefinementGenerators Q₁.toAlgebraExtension Q₂.toAlgebraExtension)
    (α := pairRefinementMap Q₁.toAlgebraExtension Q₂.toAlgebraExtension) V s
    (comp_c_app_eq_zero (f := f) V s hs)
  have h1 := extensionOfConormalHom_ideal_adjointBase (Q₁.differenceHom Q₂) V s hk hm
  have h2 : (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
      (Opens.grothendieckTopology X.carrier) _ G (Q₁.differenceHom Q₂)).app _
        ⟨coefficientSection (f ≫ t) _ V s, hk⟩ = 0 := by
    refine (conormalRestriction_conormalDesc_app (IdealRestriction.sub.{u, u, u, u}
      (pairRefinementFst Q₁.toAlgebraExtension Q₂.toAlgebraExtension).idealRestriction
      (pairRefinementSnd Q₁.toAlgebraExtension Q₂.toAlgebraExtension).idealRestriction)
      _ _).trans ?_
    refine sub_eq_zero.2 ?_
    exact (pairRefinementFst_idealRestriction_coefficientSection Q₁ _ V s hs hk).trans
      (pairRefinementSnd_idealRestriction_coefficientSection _ Q₂ V s hs hk).symm
  refine (extensionOfConormalHom_ideal_app_eq (Q₁.differenceHom Q₂) _ ⟨_, hm⟩).trans ?_
  exact (congrArg _ (h1.trans h2)).trans (pushoutInr_zero.{u} _ _ _ _)

/-- **The difference extension of two solutions** of the lifting problem of Stacks 08U7: the
Baer difference of their extensions, whose algebra structure kills `Ker(t^♯)` and so descends to
an extension of `f⁻¹𝒪_S`-algebras. -/
def differenceExtension (Q₁ Q₂ : DeformationSolution t ht f G c) :
    AlgebraSquareZeroExtension f G :=
  AlgebraSquareZeroExtension.descendBase ht.1 (Q₁.differencePushout Q₂)
    (Q₁.differencePushout_adjointBase_eq_zero Q₂)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The class of the difference extension of two solutions, read over `S'`, is the
difference of their classes.** -/
theorem restrictBase_differenceExtension_extClass (Q₁ Q₂ : DeformationSolution t ht f G c) :
    ((Q₁.differenceExtension Q₂).restrictBase t).toPresented.extClass =
      Q₁.toAlgebraExtension.toPresented.extClass -
        Q₂.toAlgebraExtension.toPresented.extClass := by
  refine (AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom
    ((Q₁.differenceExtension Q₂).restrictBase t) (Q₁.differencePushout Q₂) (𝟙 _)
    ((Category.comp_id _).trans (baseInverseImageRingMap_comp_descendBase t ht.1 f _ _
      (Q₁.differencePushout_adjointBase_eq_zero Q₂)))
    (Category.id_comp _) (fun _ _ => rfl)).trans ?_
  exact (extClass_extensionOfConormalHom (Q₁.differenceHom Q₂)).trans
    (extClass_sub_extClass_pairRefinement Q₁.toAlgebraExtension Q₂.toAlgebraExtension).symm

/-- The Baer sum of the extension of a solution with an extension of `f⁻¹𝒪_S`-algebras read
over `S'`: the sum of the two homomorphisms `𝒥/𝒥² ⟶ 𝒢` over the common refinement. -/
abbrev sumHom (Q : DeformationSolution t ht f G c) (P : AlgebraSquareZeroExtension f G) :=
  (pairRefinementFst Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal +
    (pairRefinementSnd Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal

/-- **The Baer sum of a solution with an extension over `S` induces the prescribed map.** At a
section `s` of `Ker(t^♯)` the value is `c(s)` from the solution plus `0` from the extension,
whose algebra structure comes from `f⁻¹𝒪_S` and so kills `Ker(t^♯)`. -/
theorem sumPushout_ideal_adjointBase (Q : DeformationSolution t ht f G c)
    (P : AlgebraSquareZeroExtension f G)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    (extensionOfConormalHom (Q.sumHom P)).ideal.app _
        ⟨((extensionOfConormalHom (Q.sumHom P)).adjointBase.hom.app V).hom s,
          (extensionOfConormalHom (Q.sumHom P)).adjointBase_mem_kernelIdeal V s hs⟩ =
      prescribedIdealSection c V s hs := by
  have hk := coefficientSection_mem_kernelIdeal (g := f ≫ t)
    (E := pairRefinementGenerators Q.toAlgebraExtension (P.restrictBase t))
    (α := pairRefinementMap Q.toAlgebraExtension (P.restrictBase t)) V s
    (comp_c_app_eq_zero (f := f) V s hs)
  refine (extensionOfConormalHom_ideal_adjointBase (Q.sumHom P) V s hk _).trans ?_
  have h0 : ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv _ _ (P.restrictBase t).base).hom.app V).hom s) = 0 :=
    adjointBaseHom_baseInverseImageRingMap_comp_eq_zero t f P.sheaf P.base V s hs
  have h2 : (pairRefinementSnd Q.toAlgebraExtension (P.restrictBase t)).idealRestriction.app _
      ⟨coefficientSection (f ≫ t) _ V s, hk⟩ = 0 :=
    ((pairRefinementSnd Q.toAlgebraExtension
        (P.restrictBase t)).idealRestriction_app_coefficientSection
      V s hk ((P.restrictBase t).adjointBase_mem_kernelIdeal V s hs)).trans
      ((congrArg ((P.restrictBase t).ideal.app _)
        (Subtype.ext h0 : (⟨_, (P.restrictBase t).adjointBase_mem_kernelIdeal V s hs⟩ :
          ↥(kernelIdeal (P.restrictBase t).reduction.hom _)) = 0)).trans (map_zero _))
  have hsum : (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
      (Opens.grothendieckTopology X.carrier) _ G (Q.sumHom P)).app _
        ⟨coefficientSection (f ≫ t) _ V s, hk⟩ =
      (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
        (Opens.grothendieckTopology X.carrier) _ G
        (pairRefinementFst Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal).app _
          ⟨coefficientSection (f ≫ t) _ V s, hk⟩ +
      (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
        (Opens.grothendieckTopology X.carrier) _ G
        (pairRefinementSnd Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal).app _
          ⟨coefficientSection (f ≫ t) _ V s, hk⟩ := rfl
  refine hsum.trans ?_
  refine (congrArg₂ (· + ·)
    ((conormalRestriction_conormalDesc_app _ _ _).trans
      (pairRefinementFst_idealRestriction_coefficientSection Q _ V s hs hk))
    ((conormalRestriction_conormalDesc_app _ _ _).trans h2)).trans (add_zero _)

/-- **Adding a class to a solution.** For a solution `Q` of the lifting problem of Stacks 08U7
and an extension `𝒪_{X''}` of `f⁻¹𝒪_S`-algebras, there is a solution whose class is the class
of `Q` plus the class of `𝒪_{X''}` read over `S'`: the solution defined by the Baer sum of the
two extensions. -/
theorem exists_extClass_eq_add (Q : DeformationSolution t ht f G c)
    (P : AlgebraSquareZeroExtension f G) :
    ∃ Q' : DeformationSolution t ht f G c, Q'.toAlgebraExtension.toPresented.extClass =
      Q.toAlgebraExtension.toPresented.extClass + (P.restrictBase t).toPresented.extClass := by
  have hP := extensionOfConormalHom_ideal_bijective (Q.sumHom P)
  have hc := Q.sumPushout_ideal_adjointBase P
  refine ⟨AlgebraSquareZeroExtension.toDeformationSolution hP ht hc, ?_⟩
  obtain ⟨θ, hbase, hred, hideal⟩ :=
    AlgebraSquareZeroExtension.exists_hom_toAlgebraExtension_toDeformationSolution hP ht hc
  refine (AlgebraSquareZeroExtension.extClass_eq_extClass_of_hom _ _ θ hbase hred
    hideal).symm.trans ?_
  refine (extClass_extensionOfConormalHom (Q.sumHom P)).trans ?_
  let E' := pairRefinementGenerators Q.toAlgebraExtension (P.restrictBase t)
  let α' := pairRefinementMap Q.toAlgebraExtension (P.restrictBase t)
  refine (congrArg ((PresentedSquareZeroExtension.naiveCotangentIso (f ≫ t) E' α').inv ≫ ·)
    (conormalExtClass_add (PresentedSquareZeroExtension.twoTerm (f ≫ t) E' α') G
      (pairRefinementFst Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal
      (pairRefinementSnd Q.toAlgebraExtension (P.restrictBase t)).conormalToIdeal)).trans ?_
  refine (Preadditive.comp_add _ _ _ _ _ _).trans ?_
  exact congrArg₂ (· + ·)
    (pairRefinementFst_extClass Q.toAlgebraExtension (P.restrictBase t))
    (pairRefinementSnd_extClass Q.toAlgebraExtension (P.restrictBase t))

end Derived

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
