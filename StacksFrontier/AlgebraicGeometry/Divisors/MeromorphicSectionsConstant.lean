module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.ConstantOnIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Divisors.ConstantGenericStalk
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification

/-!
# Meromorphic sections on an integral scheme are constant

Let `X` be an integral scheme with function field `R(X)` and let `F` be a quasi-coherent sheaf
of `𝒪_X`-modules. The sheaf `K_X(F)` of meromorphic sections of `F` — the extension of scalars
of `F` along `𝒪_X ⟶ K_X` — is the constant sheaf on the stalk `F_η` at the generic point, as a
sheaf of modules over the sheaf `K_X` of meromorphic functions, which by Tag 01X5 part (1) is
the constant sheaf on `R(X)`. The identification carries the canonical image of a regular
section to the constant section determined by its germ at the generic point.

## Main results

* `AlgebraicGeometry.nonempty_meromorphicSectionSheafIsoConstant`: for *every* adjunction
  exhibiting extension of scalars along `𝒪_X ⟶ K_X` as a left adjoint of restriction of
  scalars, there is an isomorphism `K_X(F) ≅ K_X ⊗ F_η` of `K_X`-modules carrying the image of
  a section under the unit of that adjunction to the constant section of its germ at the
  generic point.
* `AlgebraicGeometry.meromorphicSectionSheafIsoConstant`: a choice of that isomorphism, for the
  adjunction `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`.
* `AlgebraicGeometry.constantGenericStalkModuleSection_add` and
  `AlgebraicGeometry.constantGenericStalkModuleSection_smul`: the constant-section map is
  additive and semilinear over the function field.
* `AlgebraicGeometry.constantGenericStalkModuleSection_bijective` and
  `AlgebraicGeometry.constantGenericStalkModuleSheaf_restriction_injective`: on an open set
  containing the generic point the constant-section map is bijective, so the restriction maps
  of the constant generic-stalk module sheaf are injective there.
* `TopologicalSpace.Opens.eq_bot_of_genericPoint_notMem` and
  `CategoryTheory.SheafOfModules.subsingleton_obj_bot`: an open set of an irreducible sober
  space omitting the generic point is empty, and a sheaf of modules has a single section over
  the empty open set.

## References

* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.GenericPointDecomposition
  (genericPointStalkModuleOf meromorphicSections)

universe u

namespace TopologicalSpace.Opens

/-- An open set of an irreducible quasi-sober space that does not contain the generic point is
empty. -/
theorem eq_bot_of_genericPoint_notMem {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y]
    [QuasiSober Y] {U : Opens Y} (hU : genericPoint Y ∉ U) : U = ⊥ :=
  bot_unique fun x hx => absurd ((genericPoint_specializes x).mem_open U.isOpen hx) hU

end TopologicalSpace.Opens

namespace CategoryTheory.SheafOfModules

/-- A sheaf of modules on a topological space has only one section over the empty open set. -/
theorem subsingleton_obj_bot {Y : TopCat.{u}} (R : TopCat.Sheaf RingCat.{u} Y)
    (N : SheafOfModules.{u} R) : Subsingleton (N.val.obj (op (⊥ : Opens Y))) := by
  let S : TopCat.Sheaf AddCommGrpCat.{u} Y := ⟨N.val.presheaf, N.isSheaf⟩
  have h := TopCat.Sheaf.isTerminalOfEmpty S
  exact ⟨fun a b =>
    ((Types.isTerminalEquivUnique _ (h.isTerminalObj (forget AddCommGrpCat))).uniq a).trans
      ((Types.isTerminalEquivUnique _ (h.isTerminalObj (forget AddCommGrpCat))).uniq b).symm⟩

end CategoryTheory.SheafOfModules

namespace AlgebraicGeometry


variable (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)

private abbrev constFF : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj X.functionField

private abbrev constFFSheaf := constantSheafOnSpace X CommRingCat.{u} X.functionField

private abbrev constFFUnit : constFF X ⟶ (constFFSheaf X).obj :=
  toSheafify (Opens.grothendieckTopology X) (constFF X)

private abbrev constFFRingSheaf :=
  Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
    (J := Opens.grothendieckTopology X) (constFFSheaf X)

private abbrev constFFRingUnit :
    Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constFF X) ⟶ (constFFRingSheaf X).obj :=
  Functor.whiskerRight (constFFUnit X) (forget₂ CommRingCat.{u} RingCat.{u})

private abbrev genericStalkPresheaf :
    PresheafOfModules.{u} (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constFF X)) :=
  letI : Module X.functionField (F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  Stacks.AssociatedSheaf.constantModulePresheaf X.toRingedSpace
    (ModuleCat.of X.functionField (F.presheaf.stalk (genericPoint X)))

private abbrev genericStalkTensorPresheaf :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (constFFUnit X)).obj
    (genericStalkPresheaf X F)

private abbrev genericStalkTmulOne :
    genericStalkPresheaf X F ⟶
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (constFFUnit X)).obj
        (genericStalkTensorPresheaf X F) :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction (constFFUnit X)).unit.app
    (genericStalkPresheaf X F)

private abbrev genericStalkSheafifyUnit :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (constFFRingSheaf X).obj)).unit.app
    (genericStalkTensorPresheaf X F)

private lemma cgsSection_eq (U : X.Opens) (m : (genericStalkPresheaf X F).obj (op U)) :
    constantGenericStalkModuleSection X F U m =
      (genericStalkSheafifyUnit X F).app (op U) ((genericStalkTmulOne X F).app (op U) m) := by
  rw [Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply]
  rfl

private lemma constantSection_add (U : X.Opens)
    (m n : (genericStalkPresheaf X F).obj (op U)) :
    constantGenericStalkModuleSection X F U (m + n) =
      constantGenericStalkModuleSection X F U m +
        constantGenericStalkModuleSection X F U n := by
  rw [cgsSection_eq, cgsSection_eq, cgsSection_eq]
  exact (congrArg _ (map_add _ m n)).trans (map_add _ _ _)

private lemma constantSection_smul (U : X.Opens)
    (r : (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf (constFF X)).obj (op U))
    (m : (genericStalkPresheaf X F).obj (op U)) :
    constantGenericStalkModuleSection X F U (r • m) =
      (constFFRingUnit X).app (op U) r • constantGenericStalkModuleSection X F U m := by
  rw [cgsSection_eq, cgsSection_eq]
  refine (congrArg _ (map_smul _ r m)).trans ?_
  exact map_smul (ConcreteCategory.hom ((genericStalkSheafifyUnit X F).app (op U)))
    ((constFFRingUnit X).app (op U) r) _

/-- The constant-section map of the constant generic-stalk module sheaf is additive: the
constant section of a sum is the sum of the constant sections. -/
theorem constantGenericStalkModuleSection_add (U : X.Opens)
    (m n : F.presheaf.stalk (genericPoint X)) :
    constantGenericStalkModuleSection X F U (m + n) =
      constantGenericStalkModuleSection X F U m +
        constantGenericStalkModuleSection X F U n :=
  constantSection_add X F U m n

/-- The constant-section map of the constant generic-stalk module sheaf is semilinear over the
function field: scaling an element of the generic stalk by `r` scales its constant section over
`U` by any section `a` of the constant sheaf on the function field that is itself the constant
section of `r`. -/
theorem constantGenericStalkModuleSection_smul (U : X.Opens) (r : X.functionField)
    (a : (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X)
        (constantSheafOnSpace X CommRingCat.{u} X.functionField)).obj.obj (op U))
    (ha : a = (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U) r)
    (m : F.presheaf.stalk (genericPoint X)) :
    constantGenericStalkModuleSection X F U (r • m) =
      a • constantGenericStalkModuleSection X F U m := by
  subst ha
  exact constantSection_smul X F U r m

/-- The constant sections of the constant generic-stalk module sheaf are compatible with
restriction: the constant section of `m` over `V` is the restriction of the constant section of
`m` over any larger open set. -/
theorem constantGenericStalkModuleSection_naturality {U V : X.Opens} (i : V ⟶ U)
    (m : F.presheaf.stalk (genericPoint X)) :
    constantGenericStalkModuleSection X F V m =
      (constantGenericStalkModuleSheaf X F).val.map i.op
        (constantGenericStalkModuleSection X F U m) := by
  have h2 : (genericStalkTmulOne X F).app (op V) m =
      (genericStalkTensorPresheaf X F).map i.op ((genericStalkTmulOne X F).app (op U) m) :=
    PresheafOfModules.naturality_apply (genericStalkTmulOne X F) i.op m
  have h1 : (genericStalkSheafifyUnit X F).app (op V)
        ((genericStalkTensorPresheaf X F).map i.op ((genericStalkTmulOne X F).app (op U) m)) =
      (constantGenericStalkModuleSheaf X F).val.map i.op
        ((genericStalkSheafifyUnit X F).app (op U)
          ((genericStalkTmulOne X F).app (op U) m)) :=
    PresheafOfModules.naturality_apply (genericStalkSheafifyUnit X F) i.op _
  exact (cgsSection_eq X F V m).trans ((congrArg _ h2).trans
    (h1.trans (congrArg _ (cgsSection_eq X F U m).symm)))

private lemma constFFUnit_app_bijective (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Bijective ((constFFUnit X).app (op U)) :=
  (constantSheafOnSpaceSectionRingEquiv X X.functionField U ⟨⟨genericPoint X, hU⟩⟩).bijective


/-! ### Sections of a sheaf that is generically constant -/

private lemma mem_of_mem_generic {V : X.Opens} {x : X} (hx : x ∈ V) : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hx⟩

private lemma stalkFunctor_map_bijective_of_generic
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X} (f : P ⟶ Q)
    (hf : ∀ V : X.Opens, genericPoint X ∈ V → Function.Bijective (f.app (op V)))
    (x : X) : Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f) := by
  constructor
  · intro a b hab
    obtain ⟨V, hV, a, rfl⟩ := P.exists_germ_eq a
    obtain ⟨W, hW, b, rfl⟩ := P.exists_germ_eq b
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hab
    obtain ⟨T, hT, iV, iW, hiVW⟩ := Q.germ_eq x hV hW _ _ hab
    have hn (R : X.Opens) (k : T ⟶ R) (a : P.obj (op R)) :
        Q.map k.op (f.app (op R) a) = f.app (op T) (P.map k.op a) :=
      (CategoryTheory.congr_fun (f.naturality k.op) a).symm
    rw [hn, hn] at hiVW
    have he := (hf T (mem_of_mem_generic X hT)).1 hiVW
    rw [← P.germ_res_apply iV x hT a, ← P.germ_res_apply iW x hT b, he]
  · intro a
    obtain ⟨V, hV, a, rfl⟩ := Q.exists_germ_eq a
    obtain ⟨b, rfl⟩ := (hf V (mem_of_mem_generic X hV)).2 a
    exact ⟨P.germ V x hV b, TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _⟩

/-- On an integral scheme, a morphism from a constant presheaf of abelian groups to a sheaf
which is an isomorphism on every stalk is bijective on sections over an open set containing the
generic point. -/
private lemma bijective_app_of_isIso_stalkFunctor
    (A : AddCommGrpCat.{u}) (S : TopCat.Presheaf AddCommGrpCat.{u} X) (hS : S.IsSheaf)
    (α : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ S)
    (hα : ∀ x : X, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α))
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Bijective (α.app (op U)) := by
  classical
  have hconstantGermEq {V W : X.Opens} (hV : genericPoint X ∈ V) (hW : genericPoint X ∈ W)
      {a b : A}
      (hab : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map α).hom
          (TopCat.Presheaf.germ ((Functor.const (Opens X)ᵒᵖ).obj A) V (genericPoint X) hV a) =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map α).hom
          (TopCat.Presheaf.germ ((Functor.const (Opens X)ᵒᵖ).obj A) W (genericPoint X) hW b)) :
      a = b := by
    obtain ⟨T, hT, iTV, iTW, heq⟩ :=
      TopCat.Presheaf.germ_eq ((Functor.const (Opens X)ᵒᵖ).obj A) (genericPoint X) hV hW a b
        ((hα (genericPoint X)).1 hab)
    simpa using heq
  constructor
  · intro a b hab
    refine hconstantGermEq hU hU ?_
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact congrArg (fun s => TopCat.Presheaf.germ S U (genericPoint X) hU s) hab
  · intro s
    obtain ⟨zη, hzη⟩ := (hα (genericPoint X)).2
      (TopCat.Presheaf.germ S U (genericPoint X) hU s)
    obtain ⟨Vη, hVηgen, aη, haη⟩ :=
      TopCat.Presheaf.exists_germ_eq ((Functor.const (Opens X)ᵒᵖ).obj A) zη
    have hgeneric : TopCat.Presheaf.germ S U (genericPoint X) hU s =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map α).hom
          (TopCat.Presheaf.germ ((Functor.const (Opens X)ᵒᵖ).obj A) Vη (genericPoint X)
            hVηgen aη) := by
      rw [haη]; exact hzη.symm
    have hloc (x : U) : ∃ (V : X.Opens) (_ : V ≤ U) (hV : x.1 ∈ V) (a : A),
        TopCat.Presheaf.germ S U x.1 x.property s =
          TopCat.Presheaf.germ S V x.1 hV ((α.app (op V)).hom a) := by
      obtain ⟨zx, hzx⟩ := (hα x.1).2 (TopCat.Presheaf.germ S U x.1 x.property s)
      obtain ⟨V, hVU, hV, a, ha⟩ :=
        TopCat.Presheaf.exists_le_germ_eq ((Functor.const (Opens X)ᵒᵖ).obj A) zx x.property
      refine ⟨V, hVU, hV, a, ?_⟩
      rw [← hzx, ← ha, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    refine ⟨aη, ?_⟩
    symm
    apply TopCat.Presheaf.IsSheaf.section_ext hS
    intro x hx
    obtain ⟨V, hVU, hV, a, ha⟩ := hloc ⟨x, hx⟩
    have hVη : genericPoint X ∈ V := mem_of_mem_generic X hV
    have hspec := congrArg ((TopCat.Presheaf.stalkSpecializes S
      ((genericPoint_spec X).specializes (by trivial))).hom) ha
    have hspec' : TopCat.Presheaf.germ S U (genericPoint X) hU s =
        TopCat.Presheaf.germ S V (genericPoint X) hVη ((α.app (op V)).hom a) := by
      change (ConcreteCategory.hom (TopCat.Presheaf.germ S U x hx ≫
          TopCat.Presheaf.stalkSpecializes S
            ((genericPoint_spec X).specializes (by trivial)))) s =
        (ConcreteCategory.hom (TopCat.Presheaf.germ S V x hV ≫
          TopCat.Presheaf.stalkSpecializes S
            ((genericPoint_spec X).specializes (by trivial)))) ((α.app (op V)).hom a) at hspec
      rwa [TopCat.Presheaf.germ_stalkSpecializes,
        TopCat.Presheaf.germ_stalkSpecializes] at hspec
    have hcmp : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map α).hom
        (TopCat.Presheaf.germ ((Functor.const (Opens X)ᵒᵖ).obj A) V (genericPoint X) hVη a) =
        TopCat.Presheaf.germ S U (genericPoint X) hU s := by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact hspec'.symm
    have haa : aη = a := hconstantGermEq hVηgen hVη (hgeneric.symm.trans hcmp.symm)
    subst haa
    have hrestrict : (ConcreteCategory.hom (S.map (homOfLE hVU).op))
        ((ConcreteCategory.hom (α.app (op U))) aη) =
          (ConcreteCategory.hom (α.app (op V))) aη := by
      simpa using (α.naturality_apply (homOfLE hVU).op aη).symm
    have hgenx : TopCat.Presheaf.germ S U x hx s =
        TopCat.Presheaf.germ S U x hx ((ConcreteCategory.hom (α.app (op U))) aη) := by
      have hres := TopCat.Presheaf.germ_res_apply S (homOfLE hVU) x hV
        ((ConcreteCategory.hom (α.app (op U))) aη)
      rw [hrestrict] at hres
      exact ha.trans hres
    obtain ⟨W, hW, iWU, iWU', heq⟩ :=
      TopCat.Presheaf.germ_eq S x hx hx s ((ConcreteCategory.hom (α.app (op U))) aη) hgenx
    refine ⟨W, iWU.le, hW, ?_⟩
    rwa [Subsingleton.elim iWU iWU'] at heq


private abbrev genericStalkSheafifyAb :
    (genericStalkTensorPresheaf X F).presheaf ⟶
      (constantGenericStalkModuleSheaf X F).val.presheaf :=
  (PresheafOfModules.toPresheaf (constFFRingSheaf X).obj).map (genericStalkSheafifyUnit X F)

private lemma genericStalkSheafifyAb_isIso_stalk (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (genericStalkSheafifyAb X F)) := by
  dsimp [genericStalkSheafifyAb, genericStalkSheafifyUnit]
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (genericStalkTensorPresheaf X F).presheaf

private abbrev genericStalkTmulOneAb :
    (Functor.const (Opens X)ᵒᵖ).obj
        (AddCommGrpCat.of (F.presheaf.stalk (genericPoint X))) ⟶
      (genericStalkTensorPresheaf X F).presheaf where
  app V := AddCommGrpCat.ofHom
    ((ConcreteCategory.hom ((genericStalkTmulOne X F).app V)).toAddMonoidHom)
  naturality := by
    intro V W i
    ext m
    dsimp
    exact PresheafOfModules.naturality_apply (genericStalkTmulOne X F) i m


private lemma tensorOne_bijective {R A M : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (fun m : M => (1 : A) ⊗ₜ[R] m) := by
  let e : R ≃ₐ[R] A := AlgEquiv.ofBijective (Algebra.ofId R A) h
  let q := (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M))
  convert q.bijective using 1
  ext m
  simp [q]

private lemma genericStalkTmulOneAb_app_bijective (V : X.Opens)
    (hV : genericPoint X ∈ V) :
    Function.Bijective ((genericStalkTmulOneAb X F).app (op V)) := by
  let : Module X.functionField (F.presheaf.stalk (genericPoint X)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  let : Algebra X.functionField ((constFFSheaf X).obj.obj (op V)) :=
    ((constFFUnit X).app (op V)).hom.toAlgebra
  have h : Function.Bijective (fun m : F.presheaf.stalk (genericPoint X) =>
      (1 : (constFFSheaf X).obj.obj (op V)) ⊗ₜ[X.functionField] m) :=
    tensorOne_bijective (constFFUnit_app_bijective X V hV)
  have key : ∀ m : (genericStalkPresheaf X F).obj (op V),
      (genericStalkTmulOneAb X F).app (op V) m =
        (1 : (constFFSheaf X).obj.obj (op V)) ⊗ₜ[X.functionField] m := fun m =>
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply (constFFUnit X)
      (genericStalkPresheaf X F) (op V) m
  exact ⟨fun a b hab => h.1 ((key a).symm.trans (hab.trans (key b))),
    fun z => by obtain ⟨w, hw⟩ := h.2 z; exact ⟨w, (key w).trans hw⟩⟩

private abbrev genericStalkConstantSectionNat :
    (Functor.const (Opens X)ᵒᵖ).obj
        (AddCommGrpCat.of (F.presheaf.stalk (genericPoint X))) ⟶
      (constantGenericStalkModuleSheaf X F).val.presheaf :=
  genericStalkTmulOneAb X F ≫ genericStalkSheafifyAb X F

private lemma genericStalkConstantSectionNat_app (U : X.Opens)
    (m : (genericStalkPresheaf X F).obj (op U)) :
    (genericStalkConstantSectionNat X F).app (op U) m =
      constantGenericStalkModuleSection X F U m :=
  (cgsSection_eq X F U m).symm

/-- On an integral scheme, the constant-section map of the constant generic-stalk module sheaf
is bijective over every open set containing the generic point. -/
theorem constantGenericStalkModuleSection_bijective (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    Function.Bijective (constantGenericStalkModuleSection X F U) := by
  have hstalk (x : X) : Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (genericStalkConstantSectionNat X F)) := by
    have := genericStalkSheafifyAb_isIso_stalk X F x
    have h1 : Function.Bijective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (genericStalkTmulOneAb X F)) :=
      stalkFunctor_map_bijective_of_generic X _
        (fun V hV => genericStalkTmulOneAb_app_bijective X F V hV) x
    have h2 : Function.Bijective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (genericStalkSheafifyAb X F)) :=
      ConcreteCategory.bijective_of_isIso _
    rw [Functor.map_comp]
    exact h2.comp h1
  have hbij := bijective_app_of_isIso_stalkFunctor X
    (AddCommGrpCat.of (F.presheaf.stalk (genericPoint X)))
    (constantGenericStalkModuleSheaf X F).val.presheaf
    (constantGenericStalkModuleSheaf X F).isSheaf
    (genericStalkConstantSectionNat X F) hstalk U hU
  refine ⟨fun a b hab => hbij.1 ((genericStalkConstantSectionNat_app X F U a).trans
    (hab.trans (genericStalkConstantSectionNat_app X F U b).symm)), fun z => ?_⟩
  obtain ⟨w, hw⟩ := hbij.2 z
  exact ⟨w, (genericStalkConstantSectionNat_app X F U w).symm.trans hw⟩

/-- The restriction maps of the constant generic-stalk module sheaf between open sets
containing the generic point are injective. -/
theorem constantGenericStalkModuleSheaf_restriction_injective {U V : X.Opens} (i : V ⟶ U)
    (hV : genericPoint X ∈ V) :
    Function.Injective ((constantGenericStalkModuleSheaf X F).val.map i.op) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (constantGenericStalkModuleSection_bijective X F U (i.le hV)).2 a
  obtain ⟨b, rfl⟩ := (constantGenericStalkModuleSection_bijective X F U (i.le hV)).2 b
  rw [← constantGenericStalkModuleSection_naturality,
    ← constantGenericStalkModuleSection_naturality] at hab
  exact congrArg _ ((constantGenericStalkModuleSection_bijective X F V hV).1 hab)


/-! ### Restriction maps of the sheaf of meromorphic sections -/

private lemma finite_irreducibleComponents_of_isIntegral :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  by_cases h : Nonempty U
  · let := h
    simpa only [irreducibleComponents_eq_singleton] using
      Set.finite_singleton (Set.univ : Set U)
  · have : IsEmpty U := not_nonempty_iff.mp h
    have : Finite (Set U) := Finite.of_subsingleton
    exact Set.toFinite _

private lemma genericPointStalkModuleOf_restriction_isIso (η : genericPoints X)
    {U V : X.Opens} (i : V ⟶ U) (hV : genericPoint X ∈ V) :
    IsIso ((genericPointStalkModuleOf X F η).presheaf.map i.op) := by
  have hη : η.1 = genericPoint X := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using η.2
  change IsIso (((Scheme.Modules.pushforward (X.fromSpecStalk η.1)).obj
    ((Scheme.Modules.pullback (X.fromSpecStalk η.1)).obj F)).presheaf.map i.op)
  rw [hη]
  set f := X.fromSpecStalk (genericPoint X) with hf
  have hpre (W : X.Opens) (hW : genericPoint X ∈ W) : (Opens.map f.base).obj W = ⊤ := by
    apply top_unique
    intro z _
    change f.base z ∈ W
    have : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) := by
      change Subsingleton (PrimeSpectrum X.functionField)
      infer_instance
    have hz : z = IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim _ _
    rw [hz, hf, X.fromSpecStalk_closedPoint]
    exact hW
  have he : (Opens.map f.base).obj V = (Opens.map f.base).obj U :=
    (hpre V hV).trans (hpre U (i.le hV)).symm
  have : IsIso ((Opens.map f.base).map i) := by
    have hid : (Opens.map f.base).map i = eqToHom he := Subsingleton.elim _ _
    rw [hid]
    infer_instance
  change IsIso (((Scheme.Modules.pullback f).obj F).presheaf.map
    ((Opens.map f.base).map i).op)
  infer_instance

private lemma meromorphicSections_restriction_isIso [F.IsQuasicoherent]
    {U V : X.Opens} (i : V ⟶ U) (hV : genericPoint X ∈ V) :
    IsIso ((meromorphicSections X F).presheaf.map i.op) := by
  classical
  let η : genericPoints X := ⟨genericPoint X, by simp [genericPoints_eq_singleton]⟩
  let : Unique (genericPoints X) :=
    { default := η
      uniq := fun x => Subtype.ext (by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using x.2) }
  let e := (nonempty_meromorphicSections_iso_product_genericPointStalks_of_isReduced X
      (finite_irreducibleComponents_of_isIntegral X) F).some ≪≫
    productUniqueIso (fun η : genericPoints X => genericPointStalkModuleOf X F η)
  let a : (meromorphicSections X F).presheaf ≅ (genericPointStalkModuleOf X F η).presheaf :=
    (Scheme.Modules.toPresheaf X).mapIso e
  have := genericPointStalkModuleOf_restriction_isIso X F η i hV
  have hh := a.hom.naturality i.op
  have hmap : IsIso (a.hom.app (op U) ≫
    (genericPointStalkModuleOf X F η).presheaf.map i.op) := inferInstance
  rw [← hh] at hmap
  exact IsIso.of_isIso_comp_right _ (a.hom.app (op V))


/-! ### Germs at the generic point -/

private lemma germ_bijective_of_restrictions {Y : TopCat.{u}}
    (P : TopCat.Presheaf AddCommGrpCat.{u} Y) (y : Y)
    (hres : ∀ {U V : Opens Y} (i : V ⟶ U), y ∈ V → Function.Bijective (P.map i.op))
    (U : Opens Y) (hU : y ∈ U) : Function.Bijective (P.germ U y hU) := by
  constructor
  · intro a b hab
    obtain ⟨W, hW, i₁, i₂, he⟩ := P.germ_eq y hU hU a b hab
    have hi : i₁ = i₂ := Subsingleton.elim _ _
    subst hi
    exact (hres i₁ hW).1 he
  · intro m
    obtain ⟨V, hV, n, rfl⟩ := P.exists_germ_eq m
    have hW : y ∈ U ⊓ V := ⟨hU, hV⟩
    let i : U ⊓ V ⟶ U := homOfLE inf_le_left
    let j : U ⊓ V ⟶ V := homOfLE inf_le_right
    obtain ⟨a, ha⟩ := (hres i hW).2 (P.map j.op n)
    refine ⟨a, (P.germ_res_apply i y hW a).symm.trans ?_⟩
    rw [ha]
    exact P.germ_res_apply j y hW n

private lemma meromorphicSections_germ_bijective [F.IsQuasicoherent] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    Function.Bijective
      ((meromorphicSections X F).presheaf.germ U (genericPoint X) hU) :=
  germ_bijective_of_restrictions _ _
    (fun i hi => by
      have := meromorphicSections_restriction_isIso X F i hi
      exact ConcreteCategory.bijective_of_isIso _) U hU

variable (adj : Stacks.Sheaves.ChangeOfRings.changeOfRings (Opens.grothendieckTopology X)
      (toTotalQuotientSheaf X.sheaf) ⊣
    SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf)))

/-- The germ map at the generic point of the sheaf of meromorphic sections, as an additive
equivalence. -/
private noncomputable def meromorphicGermEquiv [F.IsQuasicoherent] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    (meromorphicSections X F).presheaf.obj (op U) ≃+
      (meromorphicSections X F).presheaf.stalk (genericPoint X) :=
  AddEquiv.ofBijective
    ((meromorphicSections X F).presheaf.germ U (genericPoint X) hU).hom
    (meromorphicSections_germ_bijective X F U hU)

/-- The inverse of the germ map at the generic point: an element of the generic stalk of `F`
determines a meromorphic section over any open set containing the generic point. -/
private def genericLift [F.IsQuasicoherent] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    F.presheaf.stalk (genericPoint X) →+
      (meromorphicSectionSheaf X.sheaf F).val.obj (op U) :=
  (meromorphicGermEquiv X F U hU).symm.toAddMonoidHom.comp
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map
        ((Scheme.Modules.toPresheaf X).map (adj.unit.app F))).hom

private lemma genericLift_germ [F.IsQuasicoherent] (U : X.Opens)
    (hU : genericPoint X ∈ U) (m : F.val.obj (op U)) :
    genericLift X F adj U hU (F.presheaf.germ U (genericPoint X) hU m) =
      (adj.unit.app F).val.app (op U) m := by
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply U (genericPoint X) hU
    ((Scheme.Modules.toPresheaf X).map (adj.unit.app F)) m
  change (meromorphicGermEquiv X F U hU).symm
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint X)).map
      ((Scheme.Modules.toPresheaf X).map (adj.unit.app F)))
        (F.presheaf.germ U (genericPoint X) hU m)) = _
  exact (congrArg _ hg).trans ((meromorphicGermEquiv X F U hU).symm_apply_apply _)

private lemma genericLift_naturality [F.IsQuasicoherent] {U V : X.Opens} (i : V ⟶ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V)
    (m : F.presheaf.stalk (genericPoint X)) :
    (meromorphicSectionSheaf X.sheaf F).val.map i.op (genericLift X F adj U hU m) =
      genericLift X F adj V hV m := by
  apply (meromorphicSections_germ_bijective X F V hV).1
  have h1 : (meromorphicSections X F).presheaf.germ V (genericPoint X) hV
        ((meromorphicSections X F).presheaf.map i.op (genericLift X F adj U hU m)) =
      (meromorphicSections X F).presheaf.germ U (genericPoint X) hU
        (genericLift X F adj U hU m) :=
    TopCat.Presheaf.germ_res_apply _ i (genericPoint X) hV _
  refine h1.trans ?_
  exact ((meromorphicGermEquiv X F U hU).apply_symm_apply _).trans
    ((meromorphicGermEquiv X F V hV).apply_symm_apply _).symm


/-- A sheaf of modules on `X` has only one section over an open set missing the generic point. -/
private lemma eq_of_genericPoint_notMem {R : TopCat.Sheaf RingCat.{u} X}
    (N : SheafOfModules.{u} R) {U : (Opens X)ᵒᵖ} (h : genericPoint X ∉ U.unop)
    (a b : N.val.obj U) : a = b := by
  have : U = op ⊥ := by
    rw [← Opposite.op_unop U, Opens.eq_bot_of_genericPoint_notMem h]
  subst this
  exact @Subsingleton.elim _ (SheafOfModules.subsingleton_obj_bot R N) a b

private noncomputable def toConstantGenericStalk :
    F ⟶ (SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf))).obj
        ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat.{u})).map
              (totalQuotientSheafIsoConstant X).val.hom)).obj
          (constantGenericStalkModuleSheaf X F)) := by
  classical
  let G : X.Modules := (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf))).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (totalQuotientSheafIsoConstant X).val.hom)).obj
        (constantGenericStalkModuleSheaf X F))
  have hd : ∀ (U : (Opens X)ᵒᵖ) (h : genericPoint X ∈ U.unop) (y : F.val.obj U),
      (if hx : genericPoint X ∈ U.unop then
        (constantGenericStalkModuleSection X F U.unop
          (F.presheaf.germ U.unop (genericPoint X) hx y) : G.val.obj U) else 0) =
      constantGenericStalkModuleSection X F U.unop
        (F.presheaf.germ U.unop (genericPoint X) h y) := fun U h y => dite_eq_left h
  refine ⟨{ app := fun U => ModuleCat.ofHom (X := F.val.obj U) (Y := G.val.obj U)
              { toFun := fun m => if h : genericPoint X ∈ U.unop then
                  constantGenericStalkModuleSection X F U.unop
                    (F.presheaf.germ U.unop (genericPoint X) h m) else 0
                map_add' := ?_
                map_smul' := ?_ }
            naturality := ?_ }⟩
  · intro m n
    by_cases h : genericPoint X ∈ U.unop
    · exact (hd U h (m + n)).trans
        ((congrArg (constantGenericStalkModuleSection X F U.unop)
            (map_add (ConcreteCategory.hom
              (F.presheaf.germ U.unop (genericPoint X) h)) m n)).trans
          ((constantSection_add X F U.unop _ _).trans
            (congrArg₂ (· + ·) (hd U h m).symm (hd U h n).symm)))
    · exact eq_of_genericPoint_notMem X _ h _ _
  · intro r m
    by_cases h : genericPoint X ∈ U.unop
    · refine (hd U h (r • m)).trans ?_
      refine Eq.trans ?_ (congrArg
        (fun z : G.val.obj U => (RingHom.id ↑(X.ringCatSheaf.obj.obj U)) r • z) (hd U h m).symm)
      have hgs := congrArg (fun z => constantGenericStalkModuleSection X F U.unop z)
        (PresheafOfModules.germ_smul F.val (genericPoint X) U.unop h r m)
      refine hgs.trans ((constantSection_smul X F U.unop _ _).trans ?_)
      have hprop : ((sheafCompose (Opens.grothendieckTopology X)
              (forget₂ CommRingCat RingCat.{u})).map
            (totalQuotientSheafIsoConstant X).val.hom).hom.app (op U.unop)
            (((sheafCompose (Opens.grothendieckTopology X)
              (forget₂ CommRingCat RingCat.{u})).map
                (toTotalQuotientSheaf X.sheaf)).hom.app (op U.unop) r) =
          (constFFRingUnit X).app (op U.unop)
            (X.presheaf.germ U.unop (genericPoint X) h r) :=
        (totalQuotientSheafIsoConstant X).property U.unop r h
      exact (congrArg (fun s : (constFFRingSheaf X).obj.obj (op U.unop) =>
        s • constantGenericStalkModuleSection X F U.unop
          (F.presheaf.germ U.unop (genericPoint X) h m)) hprop).symm
    · exact eq_of_genericPoint_notMem X _ h _ _
  · intro U V i
    ext m
    by_cases hV : genericPoint X ∈ V.unop
    · have hU : genericPoint X ∈ U.unop := i.unop.le hV
      have hres : F.presheaf.germ V.unop (genericPoint X) hV (F.val.map i m) =
          F.presheaf.germ U.unop (genericPoint X) hU m :=
        TopCat.Presheaf.germ_res_apply F.presheaf i.unop (genericPoint X) hV m
      refine (hd V hV (F.val.map i m)).trans ?_
      refine (congrArg (fun z => constantGenericStalkModuleSection X F V.unop z) hres).trans ?_
      refine (constantGenericStalkModuleSection_naturality X F i.unop
        (F.presheaf.germ U.unop (genericPoint X) hU m)).trans ?_
      exact (congrArg (fun z : G.val.obj U => G.val.map i z) (hd U hU m)).symm
    · exact eq_of_genericPoint_notMem X _ hV _ _


private abbrev constRestricted :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat.{u})).map
        (totalQuotientSheafIsoConstant X).val.hom)).obj (constantGenericStalkModuleSheaf X F)

/-- The comparison morphism from the sheaf of meromorphic sections to the constant sheaf on
the generic stalk, obtained from `toConstantGenericStalk` by the adjunction. -/
private noncomputable def meromorphicSectionHomConstant :
    meromorphicSectionSheaf X.sheaf F ⟶ constRestricted X F :=
  (adj.homEquiv F (constRestricted X F)).symm (toConstantGenericStalk X F)

private lemma toConstantGenericStalk_app (U : X.Opens) (h : genericPoint X ∈ U)
    (m : F.val.obj (op U)) :
    (toConstantGenericStalk X F).val.app (op U) m =
      constantGenericStalkModuleSection X F U
        (F.presheaf.germ U (genericPoint X) h m) := by
  classical
  change (if hx : genericPoint X ∈ U then
      constantGenericStalkModuleSection X F U
        (F.presheaf.germ U (genericPoint X) hx m) else 0) = _
  exact dite_eq_left h

private lemma meromorphicSectionHomConstant_unit (U : X.Opens) (m : F.val.obj (op U))
    (h : genericPoint X ∈ U) :
    (meromorphicSectionHomConstant X F adj).val.app (op U)
        ((adj.unit.app F).val.app (op U) m) =
      constantGenericStalkModuleSection X F U
        (F.presheaf.germ U (genericPoint X) h m) := by
  have he := (Adjunction.homEquiv_apply adj F (constRestricted X F)
      (meromorphicSectionHomConstant X F adj)).symm.trans
    ((adj.homEquiv F (constRestricted X F)).apply_symm_apply (toConstantGenericStalk X F))
  have he' := congrArg (fun k => k.val.app (op U) m) he
  exact he'.trans (toConstantGenericStalk_app X F U h m)


/-! ### The inverse of the comparison -/

private noncomputable def constantSectionAddEquiv (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    F.presheaf.stalk (genericPoint X) ≃+
      (constantGenericStalkModuleSheaf X F).val.obj (op U) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (constantGenericStalkModuleSection X F U)
      (constantSection_add X F U))
    (constantGenericStalkModuleSection_bijective X F U hU)

private lemma constantSectionAddEquiv_apply (U : X.Opens) (hU : genericPoint X ∈ U)
    (s : F.presheaf.stalk (genericPoint X)) :
    constantSectionAddEquiv X F U hU s = constantGenericStalkModuleSection X F U s := rfl

private noncomputable def inverseConstantApp [F.IsQuasicoherent] (U : (Opens X)ᵒᵖ) :
    (constantGenericStalkModuleSheaf X F).val.presheaf.obj U ⟶
      (meromorphicSectionSheaf X.sheaf F).val.presheaf.obj U := by
  classical
  exact if hU : genericPoint X ∈ U.unop then
    AddCommGrpCat.ofHom ((genericLift X F adj U.unop hU).comp
      (constantSectionAddEquiv X F U.unop hU).symm.toAddMonoidHom)
  else 0

private lemma inverseConstantApp_eq_of_mem [F.IsQuasicoherent] (U : (Opens X)ᵒᵖ)
    (hU : genericPoint X ∈ U.unop) :
    inverseConstantApp X F adj U = AddCommGrpCat.ofHom
      ((genericLift X F adj U.unop hU).comp
        (constantSectionAddEquiv X F U.unop hU).symm.toAddMonoidHom) := by
  classical
  change (if hx : genericPoint X ∈ U.unop then
      AddCommGrpCat.ofHom ((genericLift X F adj U.unop hx).comp
        (constantSectionAddEquiv X F U.unop hx).symm.toAddMonoidHom) else 0) = _
  exact dite_eq_left hU

private lemma inverseConstantApp_section [F.IsQuasicoherent] (U : (Opens X)ᵒᵖ)
    (hU : genericPoint X ∈ U.unop) (s : F.presheaf.stalk (genericPoint X)) :
    inverseConstantApp X F adj U
        (constantGenericStalkModuleSection X F U.unop s) =
      genericLift X F adj U.unop hU s := by
  rw [inverseConstantApp_eq_of_mem X F adj U hU]
  change (genericLift X F adj U.unop hU)
    ((constantSectionAddEquiv X F U.unop hU).symm
      (constantGenericStalkModuleSection X F U.unop s)) = _
  rw [show constantGenericStalkModuleSection X F U.unop s =
    constantSectionAddEquiv X F U.unop hU s from rfl, AddEquiv.symm_apply_apply]

private lemma inverseConstantApp_unit [F.IsQuasicoherent] (U : (Opens X)ᵒᵖ)
    (hU : genericPoint X ∈ U.unop) (m : F.val.obj U) :
    inverseConstantApp X F adj U
        ((toConstantGenericStalk X F).val.app U m) =
      (adj.unit.app F).val.app U m := by
  rw [toConstantGenericStalk_app X F U.unop hU m,
    inverseConstantApp_section X F adj U hU, genericLift_germ]


/-! ### Local descriptions -/

private lemma meromorphicFunction_locally_fromStructure (U : X.Opens)
    (hU : genericPoint X ∈ U)
    (r : (totalQuotientSheaf X.sheaf).obj.obj (op U)) :
    ∃ (V : X.Opens) (_hV : genericPoint X ∈ V) (i : V ⟶ U) (a : Γ(X, V)),
      (totalQuotientSheaf X.sheaf).obj.map i.op r =
        (toTotalQuotientSheaf X.sheaf).hom.app (op V) a := by
  classical
  obtain ⟨t, ht⟩ := (constFFUnit_app_bijective X U hU).2
    ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U) r)
  obtain ⟨V, hV, a, ha⟩ := X.presheaf.exists_germ_eq t
  have hW : genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
  refine ⟨U ⊓ V, hW, homOfLE inf_le_left, X.presheaf.map (homOfLE inf_le_right).op a, ?_⟩
  have : IsIso ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op (U ⊓ V))) :=
    (((sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).mapIso
      (totalQuotientSheafIsoConstant X).val).app (op (U ⊓ V))).isIso_hom
  apply (ConcreteCategory.bijective_of_isIso
    ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op (U ⊓ V)))).1
  have hnat : (totalQuotientSheafIsoConstant X).val.hom.hom.app (op (U ⊓ V))
        ((totalQuotientSheaf X.sheaf).obj.map (homOfLE inf_le_left :
          U ⊓ V ⟶ U).op r) =
      (constantSheafOnSpace X CommRingCat.{u} X.functionField).obj.map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
        ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U) r) :=
    CategoryTheory.congr_fun
      ((totalQuotientSheafIsoConstant X).val.hom.hom.naturality
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) r
  have hanat : (constFFUnit X).app (op (U ⊓ V)) t =
      (constantSheafOnSpace X CommRingCat.{u} X.functionField).obj.map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op ((constFFUnit X).app (op U) t) :=
    CategoryTheory.congr_fun
      ((constFFUnit X).naturality (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) t
  have hprop := (totalQuotientSheafIsoConstant X).property (U ⊓ V)
    (X.presheaf.map (homOfLE inf_le_right).op a) hW
  refine hnat.trans (Eq.trans ?_ hprop.symm)
  refine (congrArg (fun z => (constantSheafOnSpace X CommRingCat.{u} X.functionField).obj.map
    (homOfLE (inf_le_left : U ⊓ V ≤ U)).op z) ht.symm).trans ?_
  refine hanat.symm.trans ?_
  refine congrArg (fun z => (constFFUnit X).app (op (U ⊓ V)) z) ?_
  exact ((TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (inf_le_right : U ⊓ V ≤ V)) (genericPoint X) hW a).trans ha).symm

private lemma constantModule_locally_fromModule (U : X.Opens)
    (hU : genericPoint X ∈ U)
    (n : (constantGenericStalkModuleSheaf X F).val.obj (op U)) :
    ∃ (V : X.Opens) (_hV : genericPoint X ∈ V) (i : V ⟶ U) (m : F.val.obj (op V)),
      (constantGenericStalkModuleSheaf X F).val.map i.op n =
        (toConstantGenericStalk X F).val.app (op V) m := by
  classical
  obtain ⟨t, rfl⟩ := (constantGenericStalkModuleSection_bijective X F U hU).2 n
  obtain ⟨V, hV, m, hm⟩ := F.presheaf.exists_germ_eq t
  have hW : genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
  refine ⟨U ⊓ V, hW, homOfLE inf_le_left,
    F.val.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op m, ?_⟩
  refine (constantGenericStalkModuleSection_naturality X F
    (homOfLE (inf_le_left : U ⊓ V ≤ U)) t).symm.trans ?_
  refine Eq.trans ?_ (toConstantGenericStalk_app X F (U ⊓ V) hW _).symm
  refine congrArg _ ?_
  have hres : F.presheaf.germ (U ⊓ V) (genericPoint X) hW
      (F.val.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op m) =
      F.presheaf.germ V (genericPoint X) hV m :=
    TopCat.Presheaf.germ_res_apply F.presheaf
      (homOfLE (inf_le_right : U ⊓ V ≤ V)) (genericPoint X) hW m
  exact (hres.trans hm).symm


private noncomputable def inverseConstantPresheaf [F.IsQuasicoherent] :
    (constRestricted X F).val.presheaf ⟶
      (meromorphicSectionSheaf X.sheaf F).val.presheaf where
  app U := inverseConstantApp X F adj U
  naturality := by
    intro U V i
    ext n
    by_cases hV : genericPoint X ∈ V.unop
    · have hU : genericPoint X ∈ U.unop := i.unop.le hV
      obtain ⟨s, hs⟩ := (constantGenericStalkModuleSection_bijective X F U.unop hU).2 n
      have hres : (constRestricted X F).val.presheaf.map i n =
          constantGenericStalkModuleSection X F V.unop s := by
        refine Eq.trans ?_
          (constantGenericStalkModuleSection_naturality X F i.unop s).symm
        exact congrArg _ hs.symm
      change inverseConstantApp X F adj V ((constRestricted X F).val.presheaf.map i n) =
        (meromorphicSectionSheaf X.sheaf F).val.presheaf.map i
          (inverseConstantApp X F adj U n)
      rw [hres, inverseConstantApp_section X F adj V hV, ← hs,
        inverseConstantApp_section X F adj U hU]
      exact (genericLift_naturality X F adj i.unop hU hV s).symm
    · exact eq_of_genericPoint_notMem X _ hV _ _


private abbrev ringTQ := Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
  (J := Opens.grothendieckTopology X) (totalQuotientSheaf X.sheaf)

private abbrev ringToTQ : X.ringCatSheaf ⟶ ringTQ X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat.{u})).map (toTotalQuotientSheaf X.sheaf)

/-- On an open set containing the generic point, the inverse presheaf map carries the
image of the extension-of-scalars unit semilinearly. -/
private lemma inverseConstantApp_smul_unit [F.IsQuasicoherent] (W : X.Opens)
    (hW : genericPoint X ∈ W) (a : X.ringCatSheaf.obj.obj (op W))
    (m : F.val.obj (op W)) :
    (inverseConstantPresheaf X F adj).app (op W)
        (a • (toConstantGenericStalk X F).val.app (op W) m) =
      ((ringToTQ X).hom.app (op W) a) •
        (inverseConstantPresheaf X F adj).app (op W)
          ((toConstantGenericStalk X F).val.app (op W) m) := by
  have hγ := map_smul (ConcreteCategory.hom
    ((toConstantGenericStalk X F).val.app (op W))) a m
  have hunit := map_smul (ConcreteCategory.hom ((adj.unit.app F).val.app (op W))) a m
  refine (congrArg (fun z => (inverseConstantPresheaf X F adj).app (op W) z) hγ.symm).trans ?_
  refine (inverseConstantApp_unit X F adj (op W) hW (a • m)).trans ?_
  refine hunit.trans ?_
  exact congrArg (fun z => ((ringToTQ X).hom.app (op W) a) • z)
    (inverseConstantApp_unit X F adj (op W) hW m).symm

private lemma inverseConstantApp_smul_aux [F.IsQuasicoherent] (W : X.Opens)
    (hW : genericPoint X ∈ W)
    (rho : (ringTQ X).obj.obj (op W)) (a : X.ringCatSheaf.obj.obj (op W))
    (hrho : rho = (ringToTQ X).hom.app (op W) a)
    (t : (constRestricted X F).val.obj (op W)) (m : F.val.obj (op W))
    (ht : t = (toConstantGenericStalk X F).val.app (op W) m) :
    (inverseConstantPresheaf X F adj).app (op W) (rho • t) =
      rho • (inverseConstantPresheaf X F adj).app (op W) t := by
  subst hrho
  subst ht
  exact inverseConstantApp_smul_unit X F adj W hW a m

private lemma inverseConstantApp_smul [F.IsQuasicoherent] (U : (Opens X)ᵒᵖ)
    (r : (ringTQ X).obj.obj U) (n : (constRestricted X F).val.obj U) :
    (inverseConstantPresheaf X F adj).app U (r • n) =
      r • (inverseConstantPresheaf X F adj).app U n := by
  classical
  by_cases hU : genericPoint X ∈ U.unop
  · obtain ⟨V, hV, i, a, ha⟩ := meromorphicFunction_locally_fromStructure X U.unop hU r
    obtain ⟨W, hW, j, m, hm⟩ := constantModule_locally_fromModule X F V hV
      ((constRestricted X F).val.map i.op n)
    have hiso : IsIso ((meromorphicSectionSheaf X.sheaf F).val.presheaf.map (j ≫ i).op) :=
      meromorphicSections_restriction_isIso X F (j ≫ i) hW
    have hinj : Function.Injective
        ((meromorphicSectionSheaf X.sheaf F).val.map (j ≫ i).op) := fun x y hxy =>
      (ConcreteCategory.bijective_of_isIso
        ((meromorphicSectionSheaf X.sheaf F).val.presheaf.map (j ≫ i).op)).1 hxy
    apply hinj
    have hb : ∀ s : (constRestricted X F).val.obj U,
        (meromorphicSectionSheaf X.sheaf F).val.map (j ≫ i).op
            ((inverseConstantPresheaf X F adj).app U s) =
          (inverseConstantPresheaf X F adj).app (op W)
            ((constRestricted X F).val.map (j ≫ i).op s) := fun s =>
      (CategoryTheory.congr_fun
        ((inverseConstantPresheaf X F adj).naturality (j ≫ i).op) s).symm
    have hn : (constRestricted X F).val.map (j ≫ i).op n =
        (toConstantGenericStalk X F).val.app (op W) m :=
      (CategoryTheory.congr_fun
        ((constRestricted X F).val.presheaf.map_comp i.op j.op) n).trans hm
    have hr : (ringTQ X).obj.map (j ≫ i).op r =
        (ringToTQ X).hom.app (op W) (X.ringCatSheaf.obj.map j.op a) := by
      refine (CategoryTheory.congr_fun ((ringTQ X).obj.map_comp i.op j.op) r).trans ?_
      refine (congrArg (fun z => (ringTQ X).obj.map j.op z) ha).trans ?_
      exact (CategoryTheory.congr_fun ((ringToTQ X).hom.naturality j.op) a).symm
    have hsmulC := PresheafOfModules.map_smul (constRestricted X F).val (j ≫ i).op r n
    have hsmulM := PresheafOfModules.map_smul (meromorphicSectionSheaf X.sheaf F).val
      (j ≫ i).op r ((inverseConstantPresheaf X F adj).app U n)
    refine (hb (r • n)).trans ?_
    refine Eq.trans ?_ hsmulM.symm
    refine Eq.trans ?_
      (congrArg (fun z => (ringTQ X).obj.map (j ≫ i).op r • z) (hb n).symm)
    refine Eq.trans
      (congrArg (fun z => (inverseConstantPresheaf X F adj).app (op W) z) hsmulC) ?_
    exact inverseConstantApp_smul_aux X F adj W hW _
      (X.ringCatSheaf.obj.map j.op a) hr _ m hn
  · exact eq_of_genericPoint_notMem X _ hU _ _

private noncomputable def inverseConstant [F.IsQuasicoherent] :
    constRestricted X F ⟶ meromorphicSectionSheaf X.sheaf F :=
  ⟨PresheafOfModules.homMk (inverseConstantPresheaf X F adj)
    (inverseConstantApp_smul X F adj)⟩


private lemma meromorphicSectionHomConstant_comp_inverse [F.IsQuasicoherent] :
    meromorphicSectionHomConstant X F adj ≫ inverseConstant X F adj = 𝟙 _ := by
  classical
  refine (adj.homEquiv F (meromorphicSectionSheaf X.sheaf F)).injective ?_
  refine (Adjunction.homEquiv_apply adj F _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_apply adj F _ _).symm)
  ext U m
  by_cases hU : genericPoint X ∈ U.unop
  · exact ((congrArg (fun z => (inverseConstantPresheaf X F adj).app U z)
      (meromorphicSectionHomConstant_unit X F adj U.unop m hU)).trans
        ((inverseConstantApp_section X F adj U hU _).trans
          (genericLift_germ X F adj U.unop hU m)))
  · exact eq_of_genericPoint_notMem X _ hU _ _

private lemma inverse_comp_meromorphicSectionHomConstant [F.IsQuasicoherent] :
    inverseConstant X F adj ≫ meromorphicSectionHomConstant X F adj = 𝟙 _ := by
  classical
  ext U n
  by_cases hU : genericPoint X ∈ U.unop
  · obtain ⟨V, hV, i, m, hm⟩ := constantModule_locally_fromModule X F U.unop hU n
    refine constantGenericStalkModuleSheaf_restriction_injective X F i hV ?_
    have hfnat : (constantGenericStalkModuleSheaf X F).val.map i.op
          ((meromorphicSectionHomConstant X F adj).val.app U
            ((inverseConstantPresheaf X F adj).app U n)) =
        (meromorphicSectionHomConstant X F adj).val.app (op V)
          ((meromorphicSectionSheaf X.sheaf F).val.map i.op
            ((inverseConstantPresheaf X F adj).app U n)) :=
      (PresheafOfModules.naturality_apply
        (meromorphicSectionHomConstant X F adj).val i.op _).symm
    have hbnat : (meromorphicSectionSheaf X.sheaf F).val.map i.op
          ((inverseConstantPresheaf X F adj).app U n) =
        (inverseConstantPresheaf X F adj).app (op V)
          ((constantGenericStalkModuleSheaf X F).val.map i.op n) :=
      (CategoryTheory.congr_fun
        ((inverseConstantPresheaf X F adj).naturality i.op) n).symm
    refine hfnat.trans ?_
    refine (congrArg (fun z => (meromorphicSectionHomConstant X F adj).val.app (op V) z)
      hbnat).trans ?_
    refine (congrArg (fun z => (meromorphicSectionHomConstant X F adj).val.app (op V)
      ((inverseConstantPresheaf X F adj).app (op V) z)) hm).trans ?_
    refine (congrArg (fun z => (meromorphicSectionHomConstant X F adj).val.app (op V) z)
      (inverseConstantApp_unit X F adj (op V) hV m)).trans ?_
    refine (meromorphicSectionHomConstant_unit X F adj V m hV).trans ?_
    exact ((toConstantGenericStalk_app X F V hV m).symm).trans hm.symm
  · exact eq_of_genericPoint_notMem X _ hU _ _


/-- On an integral scheme the sheaf of meromorphic sections of a quasi-coherent module `F` is the
constant sheaf on the stalk of `F` at the generic point, read as a sheaf of modules over the sheaf
of meromorphic functions through `AlgebraicGeometry.totalQuotientSheafIsoConstant`. For every
adjunction `adj` between extension and restriction of scalars, the isomorphism may be chosen to
carry the image of a section under the unit of `adj` to the constant section determined by its
germ at the generic point. -/
@[stacks 01X5 "part (2)", ega "I 7.3.6" "integral case"]
theorem nonempty_meromorphicSectionSheafIsoConstant [F.IsQuasicoherent] :
    Nonempty { e : meromorphicSectionSheaf X.sheaf F ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (totalQuotientSheafIsoConstant X).val.hom)).obj
        (constantGenericStalkModuleSheaf X F) //
      ∀ (U : X.Opens) (m : F.val.obj (Opposite.op U))
        (h : genericPoint X ∈ U),
        (e.hom.val.app (Opposite.op U))
          ((adj.unit.app F).val.app (Opposite.op U) m) =
          constantGenericStalkModuleSection X F U
            (F.presheaf.germ U (genericPoint X) h m) } := by
  have : IsIso (meromorphicSectionHomConstant X F adj) :=
    ⟨⟨inverseConstant X F adj, meromorphicSectionHomConstant_comp_inverse X F adj,
      inverse_comp_meromorphicSectionHomConstant X F adj⟩⟩
  exact ⟨⟨asIso (meromorphicSectionHomConstant X F adj),
    fun U m h => meromorphicSectionHomConstant_unit X F adj U m h⟩⟩

/-- An isomorphism between the sheaf of meromorphic sections of a quasi-coherent module on an
integral scheme and the constant sheaf on its generic stalk, carrying the image of a section under
the unit of `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` to the constant
section determined by its germ at the generic point. -/
noncomputable def meromorphicSectionSheafIsoConstant [F.IsQuasicoherent] :
    { e : meromorphicSectionSheaf X.sheaf F ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).map
            (totalQuotientSheafIsoConstant X).val.hom)).obj
        (constantGenericStalkModuleSheaf X F) //
      ∀ (U : X.Opens) (m : F.val.obj (Opposite.op U))
        (h : genericPoint X ∈ U),
        (e.hom.val.app (Opposite.op U))
          (((Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
            (Opens.grothendieckTopology X) (toTotalQuotientSheaf X.sheaf).hom
            X.ringCatSheaf.property
            (Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).property).unit.app
              F).val.app (Opposite.op U) m) =
          constantGenericStalkModuleSection X F U
            (F.presheaf.germ U (genericPoint X) h m) } :=
  Classical.choice (nonempty_meromorphicSectionSheafIsoConstant X F
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
      (Opens.grothendieckTopology X) (toTotalQuotientSheaf X.sheaf).hom
      X.ringCatSheaf.property
      (Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).property))

end AlgebraicGeometry

end
