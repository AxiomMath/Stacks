module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassRestrictionToAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB

/-!
# The class in `H¹(U, A)` of a torsor over an object `U`

Let `(C, J)` be a site whose morphisms lie in the coefficient universe, `A` an abelian sheaf on
it and `U` an object of `C`. A torsor under `A` over `U` is a torsor under the restriction
`A|_U` of `A` to the localized site `(C/U, J/U)`. Tag 03AJ on the localized site gives its class
in `H¹(A|_U)`, and the comparison `H¹(U, A) ≅ H¹(A|_U)` of
`Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOverSheafPullback` reads it as a class in
`H¹(U, A)`, the value at `U` of Mathlib's cohomology presheaf.

This file computes that class by any short exact sequence `0 ⟶ A ⟶ E ⟶ Q ⟶ 0` of abelian sheaves
on `C` into which the torsor embeds equivariantly over a section `q ∈ Q(U)`: the class is the
boundary of `q`. As every torsor embeds in this way into an injective resolution of `A`, the
computation gives the naturality of the class in `U`: along `f : V ⟶ U`, the class of a torsor
over `V` mapping equivariantly to a torsor over `U` is the restriction of the class of the
latter.

## Main definitions

* `Stacks.Cohomology.Torsors.torsorClassOver`: the class in `H¹(U, A)` of a torsor under `A|_U`.

## Main results

* `Stacks.Cohomology.Torsors.torsorClassOver_eq_of_embedding`: **the boundary formula.** The
  class of a torsor embedded equivariantly over `q` in the middle term of a short exact sequence
  is the boundary of `q`.
* `Stacks.Cohomology.Torsors.torsorClassOver_eq_iff`: two torsors have the same class exactly
  when they are isomorphic.
* `Stacks.Cohomology.Torsors.torsorClassOver_surjective`: every class is the class of a torsor.
* `Stacks.Cohomology.Torsors.torsorClassOver_map`: **naturality.** The class of a torsor over `V`
  with an equivariant map to the restriction along `f : V ⟶ U` of a torsor over `U` is the
  restriction along `f` of the class of the latter.

## Implementation notes

The extension by zero along `Over.forget U` is Mathlib's `CategoryTheory.Functor.sheafPullback`,
which exists because the left Kan extension along `(Over.forget U).op` is computed by a coproduct
indexed by a set of morphisms `X ⟶ U`: the discrete category of these morphisms is final in the
category of costructured arrows. The same computation shows that the extension by zero is left
exact, so that restriction to `C/U` preserves injective sheaves.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w u u'

namespace Stacks.Cohomology.Torsors

/-! ### Extension by zero along `Over.forget U` -/

section ExtensionByZero

variable {C : Type u'} [Category.{u} C]

/-- The morphisms `X.unop ⟶ U`, as a discrete diagram in the category of costructured arrows of
`(Over.forget U).op` over `X`: the morphism `a` goes to `op (Over.mk a)` with the identity of
`X`. -/
def overForgetDiscreteArrows (U : C) (X : Cᵒᵖ) :
    Discrete (X.unop ⟶ U) ⥤ CostructuredArrow (Over.forget U).op X :=
  Discrete.functor fun a => CostructuredArrow.mk (Y := op (Over.mk a)) (𝟙 X)

attribute [local implicit_reducible] overForgetDiscreteArrows in
/-- The discrete diagram of morphisms `X.unop ⟶ U` is final among the costructured arrows of
`(Over.forget U).op` over `X`. -/
theorem final_overForgetDiscreteArrows (U : C) (X : Cᵒᵖ) :
    (overForgetDiscreteArrows U X).Final := by
  apply Functor.Final.mk
  intro d
  let o : StructuredArrow d (overForgetDiscreteArrows U X) :=
    StructuredArrow.mk (Y := Discrete.mk (d.hom.unop ≫ d.left.unop.hom))
      (CostructuredArrow.homMk
        (Over.homMk d.hom.unop (by simp)).op (by simp [overForgetDiscreteArrows]))
  have he (Z : StructuredArrow d (overForgetDiscreteArrows U X)) :
      Z.hom.left.unop.left = d.hom.unop := by
    have h := congrArg Quiver.Hom.unop Z.hom.w
    simpa [overForgetDiscreteArrows] using h
  have hf (Z : StructuredArrow d (overForgetDiscreteArrows U X)) :
      Z.right.as = d.hom.unop ≫ d.left.unop.hom := by
    rw [← he Z]
    exact (Over.w Z.hom.left.unop).symm
  let m (Z : StructuredArrow d (overForgetDiscreteArrows U X)) : o ⟶ Z :=
    StructuredArrow.homMk (eqToHom (Discrete.ext (hf Z).symm)) (by
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      rw [he]
      simp [o, overForgetDiscreteArrows, eqToHom_map])
  exact isConnected_of_isInitial _
    (IsInitial.ofUniqueHom m (fun Z f => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)))

attribute [local instance] final_overForgetDiscreteArrows

/-- Abelian groups in the morphism universe of `C` have the colimits computing left Kan
extensions along `(Over.forget U).op`. -/
instance hasColimitsOfShape_costructuredArrow_overForget_op (U : C) (X : Cᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (Over.forget U).op X) AddCommGrpCat.{u} :=
  Functor.Final.hasColimitsOfShape_of_final (overForgetDiscreteArrows U X)

attribute [local implicit_reducible] CategoryTheory.Functor.lan in
/-- **Extension by zero of presheaves is left exact.** The left Kan extension along
`(Over.forget U).op` of presheaves of abelian groups preserves finite limits: its values are
coproducts indexed by sets of morphisms, and coproducts of abelian groups are exact. -/
theorem preservesFiniteLimits_lan_overForget_op (U : C) :
    PreservesFiniteLimits ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})) := by
  apply preservesFiniteLimits_of_evaluation
  intro X
  let : HasExactColimitsOfShape (CostructuredArrow (Over.forget U).op X)
      AddCommGrpCat.{u} := hasExactColimitsOfShape_of_final _ (overForgetDiscreteArrows U X)
  let : PreservesFiniteLimits
      (colim : (CostructuredArrow (Over.forget U).op X ⥤ AddCommGrpCat.{u}) ⥤ _) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  let e : (Over.forget U).op.lan ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj X ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
        (CostructuredArrow.proj (Over.forget U).op X) ⋙ colim :=
    NatIso.ofComponents
      (fun F => (Over.forget U).op.leftKanExtensionObjIsoColimit F X)
      (by
        intro F G f
        dsimp only [Functor.comp_map, evaluation_obj_map, Functor.whiskeringLeft_obj_obj,
          Functor.comp_obj]
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        apply colimit.hom_ext
        intro j
        rw [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
        simp only [colim_map, ι_colimMap_assoc,
          Functor.ι_leftKanExtensionObjIsoColimit_inv]
        have hunit : ((Over.forget U).op.leftKanExtensionUnit F).app j.left ≫
              ((Over.forget U).op.lan.map f).app ((Over.forget U).op.obj j.left)
            = f.app j.left ≫ ((Over.forget U).op.leftKanExtensionUnit G).app j.left := by
          exact Functor.descOfIsLeftKanExtension_fac_app ((Over.forget U).op.leftKanExtension F)
            ((Over.forget U).op.leftKanExtensionUnit F) ((Over.forget U).op.leftKanExtension G)
            (f ≫ (Over.forget U).op.leftKanExtensionUnit G) j.left
        have hnat : ((Over.forget U).op.leftKanExtension F).map j.hom ≫
              ((Over.forget U).op.lan.map f).app X
            = ((Over.forget U).op.lan.map f).app ((Over.forget U).op.obj j.left) ≫
              ((Over.forget U).op.leftKanExtension G).map j.hom :=
          ((Over.forget U).op.lan.map f).naturality j.hom
        rw [hnat, ← Category.assoc, hunit]
        exact Category.assoc _ _ _)
  exact preservesFiniteLimits_of_natIso e.symm

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]

/-- **Restriction to a localized site preserves injective abelian sheaves**, for a site whose
morphisms lie in the coefficient universe: its left adjoint, the extension by zero, is left
exact. -/
instance preservesInjectiveObjects_overPullback_of_small_homs (U : C) :
    (J.overPullback AddCommGrpCat.{u} U).PreservesInjectiveObjects := by
  let := preservesFiniteLimits_lan_overForget_op U
  let L := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget U) AddCommGrpCat.{u} (J.over U) J
  let : PreservesFiniteLimits L := by
    dsimp [L, Functor.sheafPullbackConstruction.sheafPullback]
    infer_instance
  let : L.PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape L
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget U) AddCommGrpCat.{u} (J.over U) J)

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction to a localized site is right exact on abelian sheaves. -/
instance preservesFiniteColimits_overPullback_of_small_homs (U : C) :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{u} U) :=
  LocalizedSite.preservesFiniteColimits_overPullback J U

end ExtensionByZero

/-! ### The class of a torsor over an object -/

section Class

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison `H¹(U, A) ≃ H¹(A|_U)` used to read classes of torsors over `U`. -/
abbrev overClassEquiv (A : Sheaf J AddCommGrpCat.{u}) (U : C) :
    Sheaf.H' A 1 U ≃+ Sheaf.H.{w} (A.over U) 1 :=
  OverObjectCohomology.h'AddEquivHOverSheafPullback J U A 1

/-- **The class in `H¹(U, A)` of a torsor over `U`**: the class of Tag 03AJ of a torsor under the
restriction `A|_U` of `A` to the localized site, read in `H¹(U, A)`. -/
def torsorClassOver (A : Sheaf J AddCommGrpCat.{u}) {U : C} (T : AbelianTorsor (A.over U)) :
    Sheaf.H' A 1 U :=
  (overClassEquiv J A U).symm (torsorPushoutClass (A.over U) T)

/-- A section of `A` over `U`, read as a section of the restriction `A|_U` over the terminal
object `(U, 𝟙)` of the localized site. -/
def terminalSection (A : Sheaf J AddCommGrpCat.{u}) {U : C} (x : A.obj.obj (op U)) :
    (A.over U).obj.obj (op (Over.mk (𝟙 U))) :=
  x

/-- The morphism from the constant presheaf `ℤ` on `C/U` to the restriction of `A` sending `n`
to `n` times the restriction of a section `x` of `A|_U` over the terminal object. -/
def sectionConstMap (A : Sheaf J AddCommGrpCat.{u}) {U : C}
    (x : (A.over U).obj.obj (op (Over.mk (𝟙 U)))) :
    (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (A.over U).obj where
  app W := AddCommGrpCat.ofHom ((zmultiplesHom ((A.over U).obj.obj W)
    ((A.over U).obj.map (Over.mkIdTerminal.from W.unop).op x)).comp
      AddEquiv.ulift.toAddMonoidHom)
  naturality W W' g := by
    ext ⟨n⟩
    change n • (A.over U).obj.map (Over.mkIdTerminal.from W'.unop).op x =
      (A.over U).obj.map g (n • (A.over U).obj.map (Over.mkIdTerminal.from W.unop).op x)
    have hg : (Over.mkIdTerminal.from W'.unop).op = (Over.mkIdTerminal.from W.unop).op ≫ g :=
      Quiver.Hom.unop_inj (Over.mkIdTerminal.hom_ext _ _)
    rw [map_zsmul, hg, Functor.map_comp, ConcreteCategory.comp_apply]

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] in
lemma sectionConstMap_app_one (A : Sheaf J AddCommGrpCat.{u}) {U : C}
    (x : (A.over U).obj.obj (op (Over.mk (𝟙 U)))) (W : (Over U)ᵒᵖ) :
    (sectionConstMap J A x).app W ⟨1⟩ = (A.over U).obj.map (Over.mkIdTerminal.from W.unop).op x :=
  one_zsmul _

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] in
/-- The value at `(W, a)` of the morphism attached to a section `x ∈ A(U)` is the restriction
of `x` along `a`. -/
lemma sectionConstMap_terminalSection_app_one (A : Sheaf J AddCommGrpCat.{u}) {U : C}
    (x : A.obj.obj (op U)) (W : (Over U)ᵒᵖ) :
    ((sectionConstMap J A (terminalSection J A x)).app W ⟨1⟩ : A.obj.obj (op W.unop.left)) =
      A.obj.map W.unop.hom.op x := by
  have h : Over.mkIdTerminal.from W.unop = Over.homMk W.unop.hom (Category.comp_id _) :=
    Over.mkIdTerminal.hom_ext _ _
  refine (sectionConstMap_app_one J A _ W).trans ?_
  rw [h]
  rfl

/-- The comparison `H¹(U, A) ≃ H¹(A|_U)`, computed: apply the restriction functor, then compose
with the map from the constant sheaf `ℤ` on `C/U` to the restriction of the free abelian sheaf on
`U`. -/
lemma overClassEquiv_apply (A : Sheaf J AddCommGrpCat.{u}) (U : C) (y : Sheaf.H' A 1 U) :
    overClassEquiv J A U y =
      (Ext.mk₀ ((TerminalCohomology.freeOfTerminalIsoConstantSheaf (J.over U) (Over.mk (𝟙 U))
          Over.mkIdTerminal).inv ≫
        (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J).unit.app
          (OverObjectCohomology.freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ≫
        (J.overPullback AddCommGrpCat.{u} U).map
          (OverObjectCohomology.freeYonedaSheafOverIso J U
            (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U)
              J)).hom)).comp
        (y.mapExactFunctor (J.overPullback AddCommGrpCat.{u} U)) (zero_add 1) := by
  have key : ∀ y' : Ext (OverObjectCohomology.freeYonedaSheaf J U) A 1,
      (Ext.mk₀ (TerminalCohomology.freeOfTerminalIsoConstantSheaf (J.over U) (Over.mk (𝟙 U))
          Over.mkIdTerminal).inv).comp ((Ext.mk₀
        ((Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J).unit.app
          (OverObjectCohomology.freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))))).comp
        (((Ext.mk₀ (OverObjectCohomology.freeYonedaSheafOverIso J U
            (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U)
              J)).hom).comp y' (zero_add 1)).mapExactFunctor
          (J.overPullback AddCommGrpCat.{u} U)) (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ ((TerminalCohomology.freeOfTerminalIsoConstantSheaf (J.over U) (Over.mk (𝟙 U))
          Over.mkIdTerminal).inv ≫
        (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J).unit.app
          (OverObjectCohomology.freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ≫
        (J.overPullback AddCommGrpCat.{u} U).map
          (OverObjectCohomology.freeYonedaSheafOverIso J U
            (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U)
              J)).hom)).comp
        (y'.mapExactFunctor (J.overPullback AddCommGrpCat.{u} U)) (zero_add 1) := by
    intro y'
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
      Ext.mk₀_comp_mk₀_assoc, Category.assoc]
  exact key y

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The degree-zero part of the boundary formula: the map from the constant sheaf `ℤ` on `C/U`
attached to a section `q ∈ Q(U)` is the composite of the comparison of corepresenting sheaves
with the restriction of the morphism `ℤ_U ⟶ Q` attached to `q`. -/
lemma overClassEquiv_degreeZero (Q : Sheaf J AddCommGrpCat.{u}) (U : C) (q : Q.obj.obj (op U)) :
    (TerminalCohomology.freeOfTerminalIsoConstantSheaf (J.over U) (Over.mk (𝟙 U))
          Over.mkIdTerminal).inv ≫
        (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J).unit.app
          (OverObjectCohomology.freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ≫
        (J.overPullback AddCommGrpCat.{u} U).map
          (OverObjectCohomology.freeYonedaSheafOverIso J U
            (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U)
              J)).hom ≫
        (J.overPullback AddCommGrpCat.{u} U).map
          ((OverObjectCohomology.freeYonedaSheafHomEquiv J U Q).symm q) =
      ((sheafificationAdjunction (J.over U) AddCommGrpCat.{u}).homEquiv _ (Q.over U)).symm
        (sectionConstMap J Q (terminalSection J Q q)) := by
  set adj := Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u} (J.over U) J
  set ψ := TerminalCohomology.freeOfTerminalIsoConstantSheaf (J.over U) (Over.mk (𝟙 U))
    Over.mkIdTerminal
  rw [← Functor.map_comp]
  suffices key : adj.unit.app (OverObjectCohomology.freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ≫
      (J.overPullback AddCommGrpCat.{u} U).map
        ((OverObjectCohomology.freeYonedaSheafOverIso J U adj).hom ≫
          (OverObjectCohomology.freeYonedaSheafHomEquiv J U Q).symm q) =
      ψ.hom ≫ ((sheafificationAdjunction (J.over U) AddCommGrpCat.{u}).homEquiv _ (Q.over U)).symm
        (sectionConstMap J Q (terminalSection J Q q)) by
    rw [key]
    exact Iso.inv_hom_id_assoc ψ _
  apply (OverObjectCohomology.freeYonedaSheafHomEquiv (J.over U) (Over.mk (𝟙 U))
    ((J.overPullback AddCommGrpCat.{u} U).obj Q)).injective
  have hφ : (OverObjectCohomology.freeYonedaSheafOverIso J U adj).hom =
      OverObjectCohomology.homEquivOverPullback J U adj _ (𝟙 _) := rfl
  have h1 : (OverObjectCohomology.freeYonedaSheafOverIso J U adj).hom ≫
      (OverObjectCohomology.freeYonedaSheafHomEquiv J U Q).symm q =
      (adj.homEquiv _ Q).symm ((OverObjectCohomology.sliceSectionsEquiv J U Q).symm q) := by
    rw [hφ, ← OverObjectCohomology.homEquivOverPullback_comp, Category.id_comp]
    simp [OverObjectCohomology.homEquivOverPullback]
  rw [h1]
  refine (congrArg (OverObjectCohomology.freeYonedaSheafHomEquiv (J.over U) (Over.mk (𝟙 U))
    ((J.overPullback AddCommGrpCat.{u} U).obj Q)) (adj.homEquiv_unit _ _ _).symm).trans ?_
  rw [Equiv.apply_symm_apply]
  change OverObjectCohomology.sliceSectionsEquiv J U Q _ = _
  rw [Equiv.apply_symm_apply]
  refine Eq.trans ?_ (OverObjectCohomology.freeYonedaSheafHomEquiv_comp (J.over U) (Over.mk (𝟙 U))
    ψ.hom (((sheafificationAdjunction (J.over U) AddCommGrpCat.{u}).homEquiv _ (Q.over U)).symm
      (sectionConstMap J Q (terminalSection J Q q)))).symm
  rw [freeYonedaSheafHomEquiv_apply]
  have h2 : ψ.hom.hom.app (op (Over.mk (𝟙 U)))
      ((toSheafify (J.over U) (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free)).app
        (op (Over.mk (𝟙 U))) (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U))))) =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op (Over.mk (𝟙 U))) ⟨1⟩ :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (J.over U)
      (TerminalCohomology.freeYonedaIsoConstULiftInt (Over.mk (𝟙 U))
        Over.mkIdTerminal).hom) (op (Over.mk (𝟙 U)))) (FreeAbelianGroup.of (𝟙 _))).symm.trans rfl
  rw [h2]
  have h3 : (((sheafificationAdjunction (J.over U) AddCommGrpCat.{u}).homEquiv _
      (Q.over U)).symm (sectionConstMap J Q (terminalSection J Q q))).hom.app
        (op (Over.mk (𝟙 U))) ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op (Over.mk (𝟙 U))) ⟨1⟩) =
      (sectionConstMap J Q (terminalSection J Q q)).app (op (Over.mk (𝟙 U))) ⟨1⟩ := by
    have h := congrArg (fun α => α.app (op (Over.mk (𝟙 U))) ⟨1⟩)
      (((sheafificationAdjunction (J.over U) AddCommGrpCat.{u}).homEquiv _
        (Q.over U)).apply_symm_apply
        (sectionConstMap J Q (terminalSection J Q q)))
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
    exact h
  refine Eq.trans ?_ h3.symm
  refine Eq.trans ?_ (sectionConstMap_app_one J Q (terminalSection J Q q) (op (Over.mk (𝟙 U)))).symm
  have h4 : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h4, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The boundary formula.** Let `0 ⟶ A ⟶ E ⟶ Q ⟶ 0` be a short exact sequence of abelian
sheaves, `q ∈ Q(U)` a section and `T` a torsor under `A|_U`. If `T` maps to `E|_U`
equivariantly for the translation action of `A` on `E`, with sections lying over the
restrictions of `q`, then the class of `T` in `H¹(U, A)` is the boundary of `q`. -/
theorem torsorClassOver_eq_of_embedding {U : C} (S : ShortComplex (Sheaf J AddCommGrpCat.{u}))
    (hS : S.ShortExact) (q : S.X₃.obj.obj (op U)) (T : AbelianTorsor (S.X₁.over U))
    (i : T.1.presheaf ⟶ (S.X₂.over U).obj ⋙ forget AddCommGrpCat.{u})
    (hi : ∀ (W : (Over U)ᵒᵖ) (a : (S.X₁.over U).obj.obj W) (s : T.1.presheaf.obj W),
      let iW : T.1.presheaf.obj W → (S.X₂.over U).obj.obj W := i.app W
      iW (T.1.act W (Multiplicative.ofAdd a) s) =
        ((J.overPullback AddCommGrpCat.{u} U).map S.f).hom.app W a + iW s)
    (hq : ∀ (W : (Over U)ᵒᵖ) (s : T.1.presheaf.obj W),
      ((J.overPullback AddCommGrpCat.{u} U).map S.g).hom.app W (i.app W s) =
        (sectionConstMap J S.X₃ (terminalSection J S.X₃ q)).app W ⟨1⟩) :
    torsorClassOver J S.X₁ T =
      (Ext.mk₀ ((OverObjectCohomology.freeYonedaSheafHomEquiv J U S.X₃).symm q)).comp
        hS.extClass (zero_add 1) := by
  apply (overClassEquiv J S.X₁ U).injective
  rw [torsorClassOver, AddEquiv.apply_symm_apply]
  refine (torsorPushout_extClass_eq_boundary (S.map (J.overPullback AddCommGrpCat.{u} U))
    (hS.map_of_exact (J.overPullback AddCommGrpCat.{u} U))
    (sectionConstMap J S.X₃ (terminalSection J S.X₃ q)) T i hi hq).trans ?_
  refine Eq.trans ?_ (overClassEquiv_apply J S.X₁ U _).symm
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_extClass, Ext.mk₀_comp_mk₀_assoc]
  have hd := overClassEquiv_degreeZero J S.X₃ U q
  simp only [Category.assoc] at hd ⊢
  rw [hd]
  rfl

/-- Two torsors over `U` have the same class exactly when they are isomorphic. -/
theorem torsorClassOver_eq_iff (A : Sheaf J AddCommGrpCat.{u}) {U : C}
    (T₁ T₂ : AbelianTorsor (A.over U)) :
    torsorClassOver J A T₁ = torsorClassOver J A T₂ ↔ T₁.IsIsomorphic T₂ := by
  rw [torsorClassOver, torsorClassOver, (overClassEquiv J A U).symm.injective.eq_iff]
  constructor
  · intro h
    exact Quotient.exact (torsorIsoClassesToH1_injective (A.over U)
      (a₁ := Quotient.mk (torsorSetoid (A.over U)) T₁)
      (a₂ := Quotient.mk (torsorSetoid (A.over U)) T₂) h)
  · rintro ⟨e, -⟩
    exact torsorPushoutClass_eq_of_hom _ _ _ e

/-- Every class in `H¹(U, A)` is the class of a torsor over `U`. -/
theorem torsorClassOver_surjective (A : Sheaf J AddCommGrpCat.{u}) (U : C) :
    Function.Surjective (torsorClassOver J A (U := U)) := by
  intro x
  obtain ⟨c, hc⟩ := torsorIsoClassesToH1_surjective (A.over U) (overClassEquiv J A U x)
  obtain ⟨T, rfl⟩ := Quotient.exists_rep c
  exact ⟨T, (overClassEquiv J A U).symm_apply_eq.mpr hc⟩

/-- An injective resolution `0 ⟶ A ⟶ I ⟶ I/A ⟶ 0` of an abelian sheaf, chosen once. -/
abbrev injectiveExtension (A : Sheaf J AddCommGrpCat.{u}) :
    ShortComplex (Sheaf J AddCommGrpCat.{u}) :=
  ShortComplex.mk (Classical.arbitrary (InjectivePresentation A)).f
    (cokernel.π (Classical.arbitrary (InjectivePresentation A)).f)
    (cokernel.condition _)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma injectiveExtension_shortExact (A : Sheaf J AddCommGrpCat.{u}) :
    (injectiveExtension J A).ShortExact := by
  have := (Classical.arbitrary (InjectivePresentation A)).mono
  exact { exact := ShortComplex.exact_cokernel _ }

instance (A : Sheaf J AddCommGrpCat.{u}) : Injective (injectiveExtension J A).X₂ :=
  (Classical.arbitrary (InjectivePresentation A)).injective

/-- **Every torsor over `U` embeds into the injective resolution**, equivariantly and over a
section of the quotient over `U`. -/
theorem exists_embedding_injectiveExtension (A : Sheaf J AddCommGrpCat.{u}) {U : C}
    (T : AbelianTorsor (A.over U)) :
    ∃ (q : (injectiveExtension J A).X₃.obj.obj (op U))
      (i : T.1.presheaf ⟶ ((injectiveExtension J A).X₂.over U).obj ⋙ forget AddCommGrpCat.{u}),
      (∀ (W : (Over U)ᵒᵖ) (a : (A.over U).obj.obj W) (s : T.1.presheaf.obj W),
        let iW : T.1.presheaf.obj W → ((injectiveExtension J A).X₂.over U).obj.obj W := i.app W
        iW (T.1.act W (Multiplicative.ofAdd a) s) =
          ((J.overPullback AddCommGrpCat.{u} U).map (injectiveExtension J A).f).hom.app W a +
            iW s) ∧
      (∀ (W : (Over U)ᵒᵖ) (s : T.1.presheaf.obj W),
        ((J.overPullback AddCommGrpCat.{u} U).map (injectiveExtension J A).g).hom.app W
            (i.app W s) =
          (sectionConstMap J (injectiveExtension J A).X₃
            (terminalSection J (injectiveExtension J A).X₃ q)).app W ⟨1⟩) := by
  have hS := injectiveExtension_shortExact J A
  obtain ⟨q', hq'⟩ := ext_one_boundary_surjective (injectiveExtension J A) hS
    (OverObjectCohomology.freeYonedaSheaf J U) (torsorClassOver J A T)
  have hS' := hS.map_of_exact (J.overPullback AddCommGrpCat.{u} U)
  let q := OverObjectCohomology.freeYonedaSheafHomEquiv J U (injectiveExtension J A).X₃ q'
  let c := sectionConstMap J (injectiveExtension J A).X₃
    (terminalSection J (injectiveExtension J A).X₃ q)
  let Q := fiberTorsor ((injectiveExtension J A).map (J.overPullback AddCommGrpCat.{u} U)) hS' c
  have h1 := (fiberInclusion_spec
    ((injectiveExtension J A).map (J.overPullback AddCommGrpCat.{u} U)) hS' c).1
  have h2 : ∀ (W : (Over U)ᵒᵖ) (s : Q.1.presheaf.obj W),
      ((J.overPullback AddCommGrpCat.{u} U).map (injectiveExtension J A).g).hom.app W
          ((fiberInclusion ((injectiveExtension J A).map
            (J.overPullback AddCommGrpCat.{u} U)) c).app W s) = c.app W ⟨1⟩ :=
    fun W s => s.2
  have hQ : torsorClassOver J A Q = torsorClassOver J A T := by
    rw [torsorClassOver_eq_of_embedding J (injectiveExtension J A) hS q Q _ h1 h2,
      Equiv.symm_apply_apply, hq']
  obtain ⟨e, -⟩ := (torsorClassOver_eq_iff J A T Q).1 hQ.symm
  refine ⟨q, e.hom ≫ fiberInclusion ((injectiveExtension J A).map
    (J.overPullback AddCommGrpCat.{u} U)) c, fun W a s => ?_, fun W s => h2 W _⟩
  change (fiberInclusion ((injectiveExtension J A).map (J.overPullback AddCommGrpCat.{u} U)) c).app
    W (e.hom.app W (T.1.act W (Multiplicative.ofAdd a) s)) = _
  exact (congrArg (fun t => (fiberInclusion ((injectiveExtension J A).map
    (J.overPullback AddCommGrpCat.{u} U)) c).app W t)
      (e.map_act W (Multiplicative.ofAdd a) s)).trans
    (h1 W a _)

omit [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] in
/-- The morphism `ℤ_V ⟶ Q` attached to the restriction of a section `q ∈ Q(U)` along `f : V ⟶ U`
is the morphism attached to `q`, precomposed with `ℤ_f : ℤ_V ⟶ ℤ_U`. -/
lemma freeYonedaSheafHomEquiv_symm_map (Q : Sheaf J AddCommGrpCat.{u}) {U V : C} (f : V ⟶ U)
    (q : Q.obj.obj (op U)) :
    (OverObjectCohomology.freeYonedaSheafHomEquiv J V Q).symm (Q.obj.map f.op q) =
      (presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫
        (OverObjectCohomology.freeYonedaSheafHomEquiv J U Q).symm q := by
  apply (OverObjectCohomology.freeYonedaSheafHomEquiv J V Q).injective
  rw [Equiv.apply_symm_apply, freeYonedaSheafHomEquiv_apply]
  set q' := (OverObjectCohomology.freeYonedaSheafHomEquiv J U Q).symm q
  have hq : q = q'.hom.app (op U) ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
      (FreeAbelianGroup.of (𝟙 U))) := by
    rw [← freeYonedaSheafHomEquiv_apply, Equiv.apply_symm_apply]
  have e1 : ((presheafToSheaf J AddCommGrpCat.{u}).map
        (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)).hom.app (op V)
        ((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)
          (FreeAbelianGroup.of (𝟙 V))) =
      (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V)
        ((Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free).app (op V)
          (FreeAbelianGroup.of (𝟙 V))) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality J
      (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)) (op V)) _).symm
  have e2 : (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free).app (op V)
      (FreeAbelianGroup.of (𝟙 V)) =
      (yoneda.obj U ⋙ AddCommGrpCat.free).map f.op (FreeAbelianGroup.of (𝟙 U)) := by
    change FreeAbelianGroup.map _ (FreeAbelianGroup.of _) = FreeAbelianGroup.map _ _
    simp
  have e3 := NatTrans.naturality_apply (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)) f.op
    (FreeAbelianGroup.of (𝟙 U))
  have e4 := NatTrans.naturality_apply q'.hom f.op
    ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U)))
  calc Q.obj.map f.op q
      = Q.obj.map f.op (q'.hom.app (op U) ((toSheafify J (yoneda.obj U ⋙
          AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U)))) := congrArg _ hq
    _ = q'.hom.app (op V) ((OverObjectCohomology.freeYonedaSheaf J U).obj.map f.op
          ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
            (FreeAbelianGroup.of (𝟙 U)))) := e4.symm
    _ = q'.hom.app (op V) ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V)
          ((yoneda.obj U ⋙ AddCommGrpCat.free).map f.op (FreeAbelianGroup.of (𝟙 U)))) :=
        congrArg _ e3.symm
    _ = q'.hom.app (op V) ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V)
          ((Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free).app (op V)
            (FreeAbelianGroup.of (𝟙 V)))) := by rw [e2]
    _ = q'.hom.app (op V) (((presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)).hom.app (op V)
          ((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)
            (FreeAbelianGroup.of (𝟙 V)))) := congrArg _ e1.symm
    _ = _ := rfl

/-- **Naturality of the class of a torsor over an object.** Let `f : V ⟶ U`, let `T` be a torsor
over `U` and `T'` a torsor over `V`, and let `ρ` be an equivariant morphism from `T'` to the
restriction of `T` along `f`. Then the class of `T'` in `H¹(V, A)` is the restriction along `f`
of the class of `T` in `H¹(U, A)`. -/
theorem torsorClassOver_map (A : Sheaf J AddCommGrpCat.{u}) {U V : C} (f : V ⟶ U)
    (T : AbelianTorsor (A.over U)) (T' : AbelianTorsor (A.over V))
    (ρ : ∀ W : (Over V)ᵒᵖ, T'.1.presheaf.obj W → T.1.presheaf.obj (op ((Over.map f).obj W.unop)))
    (hρ : ∀ {W W' : (Over V)ᵒᵖ} (g : W ⟶ W') (s : T'.1.presheaf.obj W),
      ρ W' (T'.1.presheaf.map g s) = T.1.presheaf.map ((Over.map f).map g.unop).op (ρ W s))
    (hact : ∀ (W : (Over V)ᵒᵖ) (a : (A.over V).obj.obj W) (s : T'.1.presheaf.obj W),
      ρ W (T'.1.act W (Multiplicative.ofAdd a) s) =
        T.1.act (op ((Over.map f).obj W.unop)) (Multiplicative.ofAdd a) (ρ W s)) :
    torsorClassOver J A T' = (A.cohomologyPresheaf 1).map f.op (torsorClassOver J A T) := by
  obtain ⟨q, i, hi, hq⟩ := exists_embedding_injectiveExtension J A T
  have hS := injectiveExtension_shortExact J A
  let i' : T'.1.presheaf ⟶ ((injectiveExtension J A).X₂.over V).obj ⋙ forget AddCommGrpCat.{u} :=
    { app W := ↾fun s => i.app (op ((Over.map f).obj W.unop)) (ρ W s)
      naturality W W' g := by
        ext s
        change i.app _ (ρ W' (T'.1.presheaf.map g s)) = _
        rw [hρ]
        exact ConcreteCategory.congr_hom (i.naturality ((Over.map f).map g.unop).op) (ρ W s) }
  have hi' : ∀ (W : (Over V)ᵒᵖ) (a : ((injectiveExtension J A).X₁.over V).obj.obj W)
      (s : T'.1.presheaf.obj W),
      let iW : T'.1.presheaf.obj W → ((injectiveExtension J A).X₂.over V).obj.obj W := i'.app W
      iW (T'.1.act W (Multiplicative.ofAdd a) s) =
        ((J.overPullback AddCommGrpCat.{u} V).map (injectiveExtension J A).f).hom.app W a +
          iW s := by
    intro W a s
    dsimp only
    change i.app _ (ρ W (T'.1.act W (Multiplicative.ofAdd a) s)) = _
    rw [hact]
    exact hi (op ((Over.map f).obj W.unop)) a (ρ W s)
  have hq' : ∀ (W : (Over V)ᵒᵖ) (s : T'.1.presheaf.obj W),
      ((J.overPullback AddCommGrpCat.{u} V).map (injectiveExtension J A).g).hom.app W
          (i'.app W s) =
        (sectionConstMap J (injectiveExtension J A).X₃ (terminalSection J _
          ((injectiveExtension J A).X₃.obj.map f.op q))).app W ⟨1⟩ := by
    intro W s
    have e : (injectiveExtension J A).X₃.obj.map ((Over.map f).obj W.unop).hom.op q =
        (injectiveExtension J A).X₃.obj.map W.unop.hom.op
          ((injectiveExtension J A).X₃.obj.map f.op q) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    exact (hq _ (ρ W s)).trans ((sectionConstMap_terminalSection_app_one J _ q _).trans
      (e.trans (sectionConstMap_terminalSection_app_one J _ _ W).symm))
  rw [torsorClassOver_eq_of_embedding J (injectiveExtension J A) hS _ T' i' hi' hq',
    torsorClassOver_eq_of_embedding J (injectiveExtension J A) hS q T i hi hq]
  refine Eq.trans ?_ (cohomologyPresheaf_map_apply A f _).symm
  rw [Ext.mk₀_comp_mk₀_assoc, freeYonedaSheafHomEquiv_symm_map]

end Class


/-! ### Restriction of a torsor along a morphism -/

section Restriction

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C}

/-- **The restriction of a torsor along `f : V ⟶ U`.** A torsor under `A|_U` gives a torsor
under `A|_V` whose sections over `(W, a)` are the sections of the given torsor over
`(W, a ≫ f)`. -/
def AbelianTorsor.restrictOver {A : Sheaf J AddCommGrpCat.{u}} {U V : C} (f : V ⟶ U)
    (T : AbelianTorsor (A.over U)) : AbelianTorsor (A.over V) :=
  ⟨{ presheaf := (Over.map f).op ⋙ T.1.presheaf
     isSheaf := ((J.overMapPullback (Type u) f).obj ⟨T.1.presheaf, T.1.isSheaf⟩).property
     act W g s := T.1.act (op ((Over.map f).obj W.unop)) g s
     one_act W s := T.1.one_act (op ((Over.map f).obj W.unop)) s
     mul_act W g h s := T.1.mul_act (op ((Over.map f).obj W.unop)) g h s
     naturality {W W'} g a s := T.1.naturality ((Over.map f).map g.unop).op a s
     simplyTransitive W hne s t := T.1.simplyTransitive (op ((Over.map f).obj W.unop)) hne s t },
   fun W => by
     obtain ⟨R, hR, hne⟩ := T.2 ((Over.map f).obj W)
     exact ⟨R.functorPullback (Over.map f),
       (Over.map f).cover_lift (J.over V) (J.over U) hR, fun W' g hg => hne hg⟩⟩

end Restriction

section RestrictionClass

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
  [∀ U : C, HasExt.{w} (Sheaf (J.over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u})] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The class of the restriction of a torsor along `f` is the restriction of its class. -/
theorem torsorClassOver_restrict (A : Sheaf J AddCommGrpCat.{u}) {U V : C} (f : V ⟶ U)
    (T : AbelianTorsor (A.over U)) :
    torsorClassOver J A (T.restrictOver f) =
      (A.cohomologyPresheaf 1).map f.op (torsorClassOver J A T) :=
  torsorClassOver_map J A f T (T.restrictOver f) (fun _ s => s) (fun _ _ => rfl) (fun _ _ _ => rfl)

end RestrictionClass

end Stacks.Cohomology.Torsors

end
