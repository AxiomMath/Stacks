module

public import StacksFrontier.CategoryTheory.Sites.CohomologyPresheafResolution
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.AugmentedAcyclicityProduct
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Injectives

/-!
# Stacks 01GE for a hypercovering, with coefficients in a presheaf of sets

Let `(C, J)` be a small site with equalizers and fibre products, let `G` be a presheaf of sets on
`C` and let `K` be a hypercovering of `G` in the sense of Stacks 09VU. The three conditions on
`K` are exactly the three local-surjectivity hypotheses of Stacks 01GE for the augmented
simplicial presheaf `F(K) ⟶ G` of `K`, and they continue to hold after multiplying that augmented
simplicial presheaf by any presheaf of sets `T`, by
`quasiIso_freeAbelianSheafResolutionAugmentation_prodConst` in the namespace
`CategoryTheory.SimplicialObject.Augmented`. So the complex of free abelian sheaves

`… ⟶ ℤ_{T × F(K_1)}^♯ ⟶ ℤ_{T × F(K_0)}^♯ ⟶ ℤ_{T × G}^♯ ⟶ 0`

is exact, for every `T`, with no hypothesis on `T` whatsoever.

This is the statement that the proof of Stacks 0D8G obtains by tensoring Stacks 01GE with a flat
sheaf of `ℤ`-modules: at `T = h_V` representable, `ℤ_{h_V × F(K_p)}^♯` is `ℤ_{F(K_p)}^♯ ⊗ ℤ_V^♯`,
and `ℤ_V^♯` is flat, so the statement here at `T = h_V` is Stacks 01GE with coefficients in
`ℤ_V^♯`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst`:
  **Stacks 01GE for a hypercovering of a presheaf, multiplied by a presheaf of sets.**
* `Stacks.CategoryTheory.Hypercovering`
  `.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst_yoneda_comp`: **the same for a
  hypercovering of the terminal presheaf at `T = h_V`, with the augmentation normalized so that
  it lands in `ℤ_V^♯`** — the presheaf of augmentation points being terminal
  (`isTerminal_toAugmentedULift_right`), the projection off the product with it is invertible
  (`isIso_prodConst_right_fst`), and `freeAbelianSheaf_obj_yoneda` identifies `ℤ_{h_V}^♯` with the
  `freeYonedaSheaf` of the cohomology presheaf on the nose.
* `Stacks.CategoryTheory.Hypercovering.prodConstLeftIsoYoneda` and
  `.freeAbelianSheafComplexProdConstIsoYoneda`: the simplicial presheaf underlying `T × A` is
  `p ↦ T × F(K_p)`, and so the complex of Stacks 01GE for `T × A` is the complex of free abelian
  sheaves on it. `.freeAbelianSheafComplexProdConstIsoYoneda_target_X` records its degree-`n`
  term, which at `T = h_V` is the right-hand side of
  `CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso`.

## Implementation notes

The augmented simplicial presheaf is
`Stacks.CategoryTheory.Hypercovering.HypercoveringOf.toAugmentedULift` rather than `.toAugmented`,
because the three hypotheses are available at that spelling: `.toAugmentedULift` lifts the values
of `.toAugmented` into the universe in which the coskeleton comparison of condition (3) is
stated. Here every universe is the one of the objects of `C`, so the lift is by `ULift` of a type
in its own universe and the two spellings carry the same information; they are not
identified here.

Every universe of Stacks 09VU is instantiated at the one of the objects of `C`, which is also the
one of its morphisms: the hypercovering is a hypercovering of a presheaf of sets valued in
`Type u`, indexed by formal coproducts over `Type u`, and the site is small. That is the only
instantiation at which the statement can be multiplied by a presheaf of sets `T` on `C` itself.

## References

* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (G : Cᵒᵖ ⥤ Type u) (K : HypercoveringOf.{u, u} J G) (T : Cᵒᵖ ⥤ Type u)

/-- **Stacks 01GE for a hypercovering of a presheaf, multiplied by a presheaf of sets.** For a
hypercovering `K` of a presheaf of sets `G` and *any* presheaf of sets `T`, the complex
`s(ℤ_{T × F(K)}^♯)` of free abelian sheaves is a resolution of `ℤ_{T × G}^♯`.

The three conditions of Stacks 09VU on `K` are the three local-surjectivity hypotheses of
Stacks 01GE for its augmented simplicial presheaf, in the form
`isLocallySurjective_toAugmentedULift_hom_app_zero`,
`isLocallySurjective_edgesToFiberProduct_toAugmentedULift` and
`isLocallySurjective_coskAdj_unit_app_toAugmentedULift`; multiplying by `T` preserves all three,
with no hypothesis on `T`.

At `T = h_V` this is the step of the source's proof of Stacks 0D8G which reads: *since `ℤ_U^#` is
a flat sheaf of `ℤ`-modules, `s(ℤ_{F(K)}^#) ⊗_ℤ ℤ_U^# ⟶ ℤ_U^#` is a quasi-isomorphism.* -/
theorem quasiIso_freeAbelianSheafResolutionAugmentation_prodConst :
    QuasiIso (SimplicialObject.Augmented.freeAbelianSheafResolutionAugmentation
      J.toGrothendieck
      (SimplicialObject.Augmented.prodConst T (K.toAugmentedULift.{u, u, u, u} J G))) :=
  SimplicialObject.Augmented.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst
    J.toGrothendieck T (K.toAugmentedULift.{u, u, u, u} J G)
    (isLocallySurjective_toAugmentedULift_hom_app_zero J G K)
    (isLocallySurjective_edgesToFiberProduct_toAugmentedULift J G K)
    (fun n hn => isLocallySurjective_coskAdj_unit_app_toAugmentedULift J G K n hn)

/-! ### The simplicial presheaf of a hypercovering at the universe of the site -/

/-- **A sectionwise universe lift of presheaves of sets into their own universe is the
identity.** -/
def presheafULiftFunctorTrivialIso :
    presheafULiftFunctor.{u, u} (C := C) ≅ 𝟭 (Cᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents
    (fun P => Functor.isoWhiskerLeft P uliftFunctorTrivial ≪≫ Functor.rightUnitor P)
    (fun _ => by ext; rfl)

/-- **At the universe of the site, the semi-representable presheaf functor of Stacks 09VU is the
formal-coproduct Yoneda embedding.** The functor of Stacks 09VU lifts the values of
`FormalCoproduct.yoneda` into `Type (max q w v)`; here all three universes are the one of the
objects of `C`, so the lift is by `ULift` of a type in its own universe. -/
def associatedPresheafFunctorYonedaIsoTrivial :
    associatedPresheafFunctor.{u, u, u, u} (C := C) ≅ FormalCoproduct.yoneda (C := C) :=
  associatedPresheafFunctorYonedaIso.{u, u} (C := C) ≪≫
    Functor.isoWhiskerLeft _ presheafULiftFunctorTrivialIso.{u} ≪≫
    Functor.rightUnitor _

/-- **The simplicial presheaf underlying the augmented simplicial presheaf of a hypercovering is
`F(K)`**, the degreewise formal-coproduct Yoneda embedding of the simplicial semi-representable
object, at the universe of the site. This is the identification under which the degree-`p` term of
the complex of Stacks 01GE is the free abelian sheaf on `F(K_p)` in the spelling
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso` uses. -/
def toAugmentedULiftLeftIsoYoneda :
    (K.toAugmentedULift.{u, u, u, u} J G).left ≅
      K.toSimplicialObject ⋙ FormalCoproduct.yoneda (C := C) :=
  K.toAugmentedULiftLeftIso.{u, u, u, u} J G ≪≫
    Functor.isoWhiskerLeft K.toSimplicialObject associatedPresheafFunctorYonedaIsoTrivial.{u}

/-- **The simplicial presheaf underlying `T × A` for the augmented simplicial presheaf `A` of a
hypercovering is `p ↦ T × F(K_p)`.** This is the degreewise shape the identification of the
`a_!`-image of the resolution of Stacks 0D78 with the complex of Stacks 01GE is stated at, and it
is an isomorphism of *simplicial* presheaves, so it is compatible with the Čech differentials. -/
def prodConstLeftIsoYoneda :
    (SimplicialObject.Augmented.prodConst T (K.toAugmentedULift.{u, u, u, u} J G)).left ≅
      K.toSimplicialObject ⋙ FormalCoproduct.yoneda (C := C) ⋙ prodConstFunctor T :=
  eqToIso (SimplicialObject.Augmented.prodConst_left T (K.toAugmentedULift.{u, u, u, u} J G)) ≪≫
    Functor.isoWhiskerRight (toAugmentedULiftLeftIsoYoneda J G K) (prodConstFunctor T) ≪≫
    Functor.associator _ _ _

/-- The degree-`p` term of the target of `prodConstLeftIsoYoneda` is `T ⨯ F(K_p)`, in that order,
on the nose. -/
theorem prodConstLeftIsoYoneda_target_obj (p : SimplexCategory) :
    (K.toSimplicialObject ⋙ FormalCoproduct.yoneda (C := C) ⋙ prodConstFunctor T).obj (op p) =
      (T ⨯ (FormalCoproduct.yoneda (C := C)).obj (K.toSimplicialObject.obj (op p))) :=
  rfl

/-- **The complex of Stacks 01GE for `T × A` is the complex of free abelian sheaves on
`p ↦ T × F(K_p)`**: the image under `freeAbelianSheafComplexFunctor` of
`prodConstLeftIsoYoneda`. -/
def freeAbelianSheafComplexProdConstIsoYoneda :
    (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        (SimplicialObject.Augmented.prodConst T
          (K.toAugmentedULift.{u, u, u, u} J G)).left ≅
      (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        (K.toSimplicialObject ⋙ FormalCoproduct.yoneda (C := C) ⋙ prodConstFunctor T) :=
  (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).mapIso
    (prodConstLeftIsoYoneda J G K T)

/-- The degree-`n` term of the target of `freeAbelianSheafComplexProdConstIsoYoneda` is the
sheafification of the free abelian presheaf on `T ⨯ F(K_n)`, on the nose.

At `T = h_V` this is the right-hand side of
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso`, which identifies
`a_! g_{n!} j_n^{-1} ℤ_V^♯` with it: so the two sides of the identification that the cohomological
descent of a hypercovering still needs are spelled the same way, and what is missing between them
is naturality in the simplex map. -/
theorem freeAbelianSheafComplexProdConstIsoYoneda_target_X (n : ℕ) :
    ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        (K.toSimplicialObject ⋙ FormalCoproduct.yoneda (C := C) ⋙
          prodConstFunctor T)).X n =
      (presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj
        ((T ⨯ (FormalCoproduct.yoneda (C := C)).obj
          (K.toSimplicialObject.obj (op (SimplexCategory.mk n)))) ⋙ AddCommGrpCat.free) :=
  rfl

section Terminal

variable (H : HypercoveringOfTerminal.{u, u} J) (V : C)

/-- The presheaf of augmentation points of a hypercovering of the terminal presheaf is terminal:
it is the terminal presheaf carried through two sectionwise universe lifts, each of which
preserves terminal objects. -/
def isTerminal_toAugmentedULift_right :
    IsTerminal (H.toAugmentedULift.{u, u, u, u} J (⊤_ (Cᵒᵖ ⥤ Type u))).right :=
  IsTerminal.isTerminalObj (presheafULiftFunctor.{u, u} (C := C)) _
    (IsTerminal.isTerminalObj
      ((Functor.whiskeringRight Cᵒᵖ (Type u) (Type u)).obj uliftFunctor.{u, u}) _
      terminalIsTerminal)

/-- The first projection off the product of a presheaf with the presheaf of augmentation points
of a hypercovering of the terminal presheaf is an isomorphism, that presheaf being terminal. -/
theorem isIso_prodConst_right_fst :
    IsIso (Limits.prod.fst (X := T)
      (Y := (H.toAugmentedULift.{u, u, u, u} J (⊤_ (Cᵒᵖ ⥤ Type u))).right)) :=
  (BinaryFan.isLimit_iff_isIso_fst (isTerminal_toAugmentedULift_right J H)
    (BinaryFan.mk (Limits.prod.fst (X := T)
        (Y := (H.toAugmentedULift.{u, u, u, u} J (⊤_ (Cᵒᵖ ⥤ Type u))).right))
      (Limits.prod.snd))).mp ⟨prodIsProd _ _⟩

omit [HasEqualizers C] in
/-- The free abelian sheaf on a representable presheaf is the sheaf `ℤ_V^♯` out of which the
cohomology presheaf takes `Ext`-groups, on the nose. This is what identifies the target of
`quasiIso_freeAbelianSheafResolutionAugmentation_prodConst_yoneda_comp` with the coefficient
sheaf the cohomological descent of a hypercovering is tested against. -/
theorem freeAbelianSheaf_obj_yoneda :
    (Presheaf.freeAbelianSheaf J.toGrothendieck).obj (yoneda.obj V) =
      Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J.toGrothendieck V :=
  rfl

/-- **Stacks 01GE for a hypercovering of the terminal presheaf, with coefficients in `ℤ_V^♯`.**
For a hypercovering `K` of the terminal presheaf and an object `V` of the site, the complex
`s(ℤ_{h_V × F(K)}^♯)` of free abelian sheaves is a resolution of `ℤ_V^♯`: the augmentation of
`quasiIso_freeAbelianSheafResolutionAugmentation_prodConst` at `T = h_V`, followed by the
identification of `ℤ_{h_V × K.right}^♯` with `ℤ_{h_V}^♯` coming from terminality of `K.right`.

This is Stacks 01GE with coefficients in the flat sheaf `ℤ_V^♯`, which is the one coefficient
case the cohomological descent of a hypercovering needs on the base site. -/
theorem quasiIso_freeAbelianSheafResolutionAugmentation_prodConst_yoneda_comp :
    QuasiIso (SimplicialObject.Augmented.freeAbelianSheafResolutionAugmentation
        J.toGrothendieck
        (SimplicialObject.Augmented.prodConst (yoneda.obj V)
          (H.toAugmentedULift.{u, u, u, u} J (⊤_ (Cᵒᵖ ⥤ Type u)))) ≫
      (ChainComplex.single₀ (Sheaf J.toGrothendieck AddCommGrpCat.{u})).map
        ((Presheaf.freeAbelianSheaf J.toGrothendieck).map
          (Limits.prod.fst (X := yoneda.obj V)
            (Y := (H.toAugmentedULift.{u, u, u, u} J (⊤_ (Cᵒᵖ ⥤ Type u))).right)))) :=
  have := quasiIso_freeAbelianSheafResolutionAugmentation_prodConst J
    (⊤_ (Cᵒᵖ ⥤ Type u)) H (yoneda.obj V)
  have := isIso_prodConst_right_fst J (yoneda.obj V) H
  inferInstance

end Terminal

end Stacks.CategoryTheory.Hypercovering

end
