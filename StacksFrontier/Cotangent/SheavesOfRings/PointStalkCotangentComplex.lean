module

public import StacksFrontier.Cotangent.SheavesOfRings.PointStalkCotangentColimit
public import StacksFrontier.Cotangent.SheavesOfRings.ProductRingsSectionwise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of the cotangent complex at a point of a site

Let `f : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and let `Φ` be a
point of the site, with stalk rings `A_Φ → B_Φ`. This file identifies the stalk at `Φ` of the
cotangent complex `L_{B/A}` of Tag 08SS with the cotangent complex `L_{B_Φ/A_Φ}` of the ring map
of stalks ([Stacks, Tag 08T0]), as complexes of `B_Φ`-modules, and proves that the identification
is natural in commutative squares of homomorphisms of sheaves of rings.

On germs, the germ at a neighbourhood `(U, x)` of the image of a class `s ∈ L_{B(U)/A(U)}` under
the canonical map of Tag 08SX goes to the image of `s` under the map of cotangent complexes induced
by the germ maps `A(U) → A_Φ`, `B(U) → B_Φ`.

## Main definitions

* `CategoryTheory.Sheaf.pointStalkCotangentTerm`: the comparison of the stalk at `Φ` of the
  presheaf `U ↦ L^n_{B(U)/A(U)}` with `L^n_{B_Φ/A_Φ}`; an isomorphism.
* `CategoryTheory.Sheaf.pointCotangentGerm`: the germ in the stalk of `L^n_{B/A}` of the image of
  a sectionwise class under the canonical map of Tag 08SX.
* `CategoryTheory.Sheaf.pointStalkCotangentComplexIso`: **the stalk of `L_{B/A}` at `Φ` is
  `L_{B_Φ/A_Φ}`**, as complexes of `B_Φ`-modules.
* `CategoryTheory.Sheaf.pointStalkSquare`: the square of stalk maps of a commutative square of
  homomorphisms of sheaves of rings.

## Main results

* `CategoryTheory.Sheaf.pointStalkCotangentComplexIso_hom_germ`: the identification on germs.
* `CategoryTheory.Sheaf.exists_pointCotangentGerm_eq`: every element of the stalk is such a germ.
* `CategoryTheory.Sheaf.sheafModuleFiberOfCommRing_map_squareCotangentComplexMap_germ` and
  `CategoryTheory.Sheaf.cotangentComplexAbMap_pointGermSquare_pointStalkSquare`: naturality in
  commutative squares, on germs: the stalk of the map of cotangent complexes of a square is, on
  germs, the map of the square on sections, and the germ squares carry it to the map of the
  square of stalk maps.

## References

* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08S9](https://stacks.math.columbia.edu/tag/08S9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{max u v w} C] (Φ : J.Point.{max u v w})
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

omit [LocallySmall.{max u v w} C] in
/-- Restricting the germ square of a neighbourhood `(V, Φ.fiber.map g x)` along `g : U ⟶ V`
gives the germ square of `(U, x)`. -/
theorem sectionsRestrictionSquare_comp_pointGermSquare {U V : C} (g : U ⟶ V)
    (x : Φ.fiber.obj U) :
    CommAlgCat.AlgebraSquare.comp.{max u v w, max u v w} (sectionsRestrictionSquare J f g.op)
        (pointGermSquare J Φ f U x) =
      pointGermSquare J Φ f V (Φ.fiber.map g x) :=
  (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr
    ⟨congrArg CommRingCat.Hom.hom (Φ.toPresheafFiber_w g x A.obj),
      congrArg CommRingCat.Hom.hom (Φ.toPresheafFiber_w g x B.obj)⟩

omit [LocallySmall.{max u v w} C] in
/-- The maps of cotangent complexes induced by the germ squares, read in degree `n`, are
compatible with the restriction maps of the presheaf `U ↦ L^n_{B(U)/A(U)}`. -/
theorem pointGermSquare_restriction (n : ℤ) {U V : C} (g : U ⟶ V) (x : Φ.fiber.obj U) :
    ((sectionwiseCotangentPresheafComplex J f).X n).map g.op ≫
        (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f V (Φ.fiber.map g x))).f n :=
  (congrArg (fun k => HomologicalComplex.Hom.f k n)
    ((CommAlgCat.cotangentComplexAbMap_comp.{max u v w} _ _).symm.trans
      (congrArg CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (sectionsRestrictionSquare_comp_pointGermSquare J Φ f g x))))

/-- The cocone over the neighbourhoods of `Φ` on the presheaf `U ↦ L^n_{B(U)/A(U)}`, with vertex
`L^n_{B_Φ/A_Φ}`, whose legs are the maps induced by the germ squares. -/
def pointStalkCotangentCocone (n : ℤ) :
    Cocone ((Functor.Elements.π Φ.fiber).op ⋙ (sectionwiseCotangentPresheafComplex J f).X n) where
  pt := (CommAlgCat.cotangentComplexAb.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).X n
  ι :=
    { app e := (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f e.unop.1 e.unop.2)).f n
      naturality e e' φ := by
        have h := pointGermSquare_restriction J Φ f n φ.unop.1 e'.unop.2
        rw [φ.unop.2] at h
        exact h.trans (Category.comp_id _).symm }

/-- The cocone of germ squares is a colimit cocone: Tag 08S9 along a directed cofinal system of
neighbourhoods. -/
theorem nonempty_isColimitPointStalkCotangentCocone (n : ℤ) :
    Nonempty (IsColimit (pointStalkCotangentCocone J Φ f n)) := by
  obtain ⟨α, _, _, _, F, _⟩ := Φ.exists_directed_final
  exact ⟨(Functor.Final.isColimitWhiskerEquiv F _)
    (AddCommGrpCat.isColimit_of_isDirectedColimitOfTypes _ _
      (isDirectedColimitOfTypes_pointStalkCotangent J Φ f F n))⟩

/-- The comparison of the stalk at `Φ` of the presheaf `U ↦ L^n_{B(U)/A(U)}` with
`L^n_{B_Φ/A_Φ}`. -/
def pointStalkCotangentTerm (n : ℤ) :
    (Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).obj
        ((sectionwiseCotangentPresheafComplex J f).X n) ⟶
      (CommAlgCat.cotangentComplexAb.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).X n :=
  colimit.desc _ (pointStalkCotangentCocone J Φ f n)

omit [LocallySmall.{max u v w} C] in
/-- On the germs at a neighbourhood `(U, x)`, the comparison is the map induced by the germ
square of `(U, x)`. -/
@[reassoc]
theorem toPresheafFiber_pointStalkCotangentTerm (n : ℤ) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x ((sectionwiseCotangentPresheafComplex J f).X n) ≫
        pointStalkCotangentTerm J Φ f n =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n :=
  colimit.ι_desc (pointStalkCotangentCocone J Φ f n) (op (Φ.fiber.elementsMk U x))

/-- **The stalk of `U ↦ L^n_{B(U)/A(U)}` at `Φ` is `L^n_{B_Φ/A_Φ}`.** -/
instance isIso_pointStalkCotangentTerm (n : ℤ) : IsIso (pointStalkCotangentTerm J Φ f n) :=
  inferInstanceAs (IsIso (colimit.isoColimitCocone
    ⟨_, (nonempty_isColimitPointStalkCotangentCocone J Φ f n).some⟩).hom)


/-! ## The stalk of `L_{B/A}` -/

section Stalk

attribute [local instance] moduleOfSections

/-- The `RingCat`-valued germ of a section of a sheaf of commutative rings is its
`CommRingCat`-valued germ, read through the comparison of the two stalks. -/
theorem commRingSheafFiberIso_inv_toPresheafFiber (O : Sheaf J CommRingCat.{max u v w}) (U : C)
    (x : Φ.fiber.obj U) (β : O.obj.obj (op U)) :
    (Stacks.commRingSheafFiberIso Φ O).inv.hom ((Φ.toPresheafFiber U x O.obj).hom β) =
      ((Φ.toPresheafFiber U x
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} O).obj).hom β :
        (Φ.presheafFiber (A := RingCat.{max u v w})).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} O).obj) := by
  have h := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) U x O.obj
  have h' := (((Φ.presheafFiberCompIso
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).app O.obj).eq_comp_inv).2 h
  exact (ConcreteCategory.congr_hom h' β).symm

/-- The germ of `β • m` in the stalk of a sheaf of `B`-modules is the germ of `β` acting on the
germ of `m`, the stalk being a module over the `CommRingCat`-valued stalk of `B`. -/
theorem smul_toPresheafModuleFiber (M : targetModules J B) (U : C) (x : Φ.fiber.obj U)
    (β : B.obj.obj (op U)) (m : M.val.obj (op U)) :
    ((Φ.toPresheafFiber U x B.obj).hom β •
        (show (Stacks.sheafModuleFiberOfCommRing Φ B).obj M from
          Stacks.toPresheafModuleFiber Φ M.val U x m)) =
      Stacks.toPresheafModuleFiber Φ M.val U x (β • m) := by
  refine Eq.trans ?_ (Stacks.toPresheafModuleFiber_smul Φ M.val U x β m).symm
  refine Eq.trans ?_ (congrArg (fun r : (Φ.presheafFiber (A := RingCat.{max u v w})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj =>
        r • Stacks.toPresheafModuleFiber Φ M.val U x m)
    (commRingSheafFiberIso_inv_toPresheafFiber J Φ B U x β))
  rfl

variable (n : ℤ)

/-- The stalk functor inverts the canonical map from `U ↦ L^n_{B(U)/A(U)}` to `L^n_{B/A}`:
sheafification inverts it (Tag 08SX), and taking stalks does not see sheafification. -/
instance isIso_presheafFiber_map_comparison :
    IsIso ((Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).map
      ((sectionwiseCotangentPresheafComplexComparison J f).f n)) :=
  Φ.W_isInvertedBy_presheafFiber _ (W_sectionwiseCotangentPresheafComplexComparison_f J f n)

/-- The identification of the stalk at `Φ` of `L^n_{B/A}` with `L^n_{B_Φ/A_Φ}`, on underlying
abelian groups. -/
def pointStalkCotangentAbIso :
    (Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).obj ((cotangentComplexAb J f).X n).obj ≅
      (CommAlgCat.cotangentComplexAb.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).X n :=
  (asIso ((Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).map
      ((sectionwiseCotangentPresheafComplexComparison J f).f n))).symm ≪≫
    asIso (pointStalkCotangentTerm J Φ f n)

/-- The germ at a neighbourhood `(U, x)` of `Φ` of the image in `L^n_{B/A}(U)` of a class of
`L^n_{B(U)/A(U)}` under the canonical map of Tag 08SX. -/
abbrev pointCotangentGermAb (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).obj ((cotangentComplexAb J f).X n).obj :=
  Φ.toPresheafFiber U x ((cotangentComplexAb J f).X n).obj
    ((sectionsCotangentComplexComparison J f (op U)).f n s)

/-- **The identification on germs.** The germ of the image of a sectionwise class `s` goes to the
image of `s` under the map induced by the germ square. -/
theorem pointStalkCotangentAbIso_germ (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (pointStalkCotangentAbIso J Φ f n).hom (pointCotangentGermAb J Φ f n U x s) =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s := by
  have h : pointCotangentGermAb J Φ f n U x s =
      (asIso ((Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).map
        ((sectionwiseCotangentPresheafComplexComparison J f).f n))).hom
        (Φ.toPresheafFiber U x ((sectionwiseCotangentPresheafComplex J f).X n) s) :=
    (Φ.toPresheafFiber_naturality_apply
      ((sectionwiseCotangentPresheafComplexComparison J f).f n) U x s).symm
  rw [h, pointStalkCotangentAbIso, Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply]
  exact ConcreteCategory.congr_hom (toPresheafFiber_pointStalkCotangentTerm J Φ f n U x) s

/-- Every element of the stalk of `L^n_{B/A}` is the germ of the image of a sectionwise class. -/
theorem exists_pointCotangentGermAb_eq
    (m : (Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).obj
      ((cotangentComplexAb J f).X n).obj) :
    ∃ (U : C) (x : Φ.fiber.obj U)
      (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
        (sectionsAlgebra J f (op U))).X n), pointCotangentGermAb J Φ f n U x s = m := by
  obtain ⟨U, x, s, hs⟩ := Φ.toPresheafFiber_jointly_surjective
    (inv ((Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).map
      ((sectionwiseCotangentPresheafComplexComparison J f).f n)) m)
  refine ⟨U, x, s, (Φ.toPresheafFiber_naturality_apply
    ((sectionwiseCotangentPresheafComplexComparison J f).f n) U x s).symm.trans ?_⟩
  rw [hs, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

omit [LocallySmall.{max u v w} C] in
/-- Germs of sectionwise classes are compatible with restriction to a smaller neighbourhood. -/
theorem pointCotangentGermAb_restrict {W U : C} (g : W ⟶ U) (z : Φ.fiber.obj W)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    pointCotangentGermAb J Φ f n U (Φ.fiber.map g z) s =
      pointCotangentGermAb J Φ f n W z
        (((sectionwiseCotangentPresheafComplex J f).X n).map g.op s) := by
  refine (Φ.toPresheafFiber_w_apply g z ((cotangentComplexAb J f).X n).obj _).symm.trans ?_
  exact congrArg (Φ.toPresheafFiber W z ((cotangentComplexAb J f).X n).obj)
    (ConcreteCategory.congr_hom
      (((sectionwiseCotangentPresheafComplexComparison J f).f n).naturality g.op) s).symm

omit [LocallySmall.{max u v w} C] in
/-- The maps of cotangent complexes induced by germ squares are semilinear over the germ map of
`B`. -/
theorem cotangentComplexAbMap_pointGermSquare_smul (U : C) (x : Φ.fiber.obj U)
    (β : B.obj.obj (op U))
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n
        (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (sectionsAlgebra J f (op U))).X n from (show sectionsAlgebra J f (op U) from β) • s) =
      (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (pointStalkAlgebra J Φ f)).X n from
        (show pointStalkAlgebra J Φ f from (Φ.toPresheafFiber U x B.obj).hom β) •
          (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
            (pointStalkAlgebra J Φ f)).X n from
            (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s)) :=
  ((CommAlgCat.squareFunctoriality (pointGermSquare J Φ f U x)).complexMap.f n).hom.map_smul β s

/-- The underlying abelian group of the stalk of a sheaf of `B`-modules is the stalk of its
underlying sheaf of abelian groups, by definition. -/
def stalkForgetIso (M : targetModules J B) :
    (forget₂ (ModuleCat.{max u v w} ((Φ.presheafFiber (A := CommRingCat)).obj B.obj))
        AddCommGrpCat.{max u v w}).obj ((Stacks.sheafModuleFiberOfCommRing Φ B).obj M) ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{max u v w})).obj
        ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).obj M).obj :=
  Iso.refl _

/-- The identification of the stalk at `Φ` of `L^n_{B/A}` with `L^n_{B_Φ/A_Φ}`, on the
underlying abelian group of the stalk module. -/
def pointStalkCotangentAddIso :
    (forget₂ (ModuleCat.{max u v w} ((Φ.presheafFiber (A := CommRingCat)).obj B.obj))
        AddCommGrpCat.{max u v w}).obj
        ((Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J f).X n)) ≅
      (CommAlgCat.cotangentComplexAb.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).X n :=
  stalkForgetIso J Φ ((cotangentComplex J f).X n) ≪≫ pointStalkCotangentAbIso J Φ f n

/-- The germ in the stalk module of `L^n_{B/A}` at a neighbourhood `(U, x)` of `Φ` of the image
in `L^n_{B/A}(U)` of a class of `L^n_{B(U)/A(U)}` under the canonical map of Tag 08SX. -/
abbrev pointCotangentGerm (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J f).X n) :=
  Stacks.toPresheafModuleFiber Φ ((cotangentComplex J f).X n).val U x
    ((sectionsCotangentComplexComparison J f (op U)).f n s)

/-- **The identification on germs.** -/
theorem pointStalkCotangentAddIso_germ (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (pointStalkCotangentAddIso J Φ f n).hom (pointCotangentGerm J Φ f n U x s) =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s :=
  pointStalkCotangentAbIso_germ J Φ f n U x s

/-- Every element of the stalk module of `L^n_{B/A}` is the germ of the image of a sectionwise
class. -/
theorem exists_pointCotangentGerm_eq
    (m : (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J f).X n)) :
    ∃ (U : C) (x : Φ.fiber.obj U)
      (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
        (sectionsAlgebra J f (op U))).X n), pointCotangentGerm J Φ f n U x s = m :=
  exists_pointCotangentGermAb_eq J Φ f n ((stalkForgetIso J Φ ((cotangentComplex J f).X n)).hom m)

/-- Germs of sectionwise classes in the stalk module are compatible with restriction. -/
theorem pointCotangentGerm_restrict {W U : C} (g : W ⟶ U) (z : Φ.fiber.obj W)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    pointCotangentGerm J Φ f n U (Φ.fiber.map g z) s =
      pointCotangentGerm J Φ f n W z
        (((sectionwiseCotangentPresheafComplex J f).X n).map g.op s) :=
  pointCotangentGermAb_restrict J Φ f n g z s

omit [LocallySmall.{max u v w} C] in
/-- Two neighbourhoods of `Φ` have a common refinement. -/
theorem exists_common_neighbourhood {U U' : C} (x : Φ.fiber.obj U) (x' : Φ.fiber.obj U') :
    ∃ (W : C) (z : Φ.fiber.obj W) (g : W ⟶ U) (g' : W ⟶ U'),
      Φ.fiber.map g z = x ∧ Φ.fiber.map g' z = x' := by
  let e₁ : (Φ.fiber.Elements)ᵒᵖ := op (Φ.fiber.elementsMk U x)
  let e₂ : (Φ.fiber.Elements)ᵒᵖ := op (Φ.fiber.elementsMk U' x')
  exact ⟨_, _, (IsFiltered.leftToMax e₁ e₂).unop.hom, (IsFiltered.rightToMax e₁ e₂).unop.hom,
    (IsFiltered.leftToMax e₁ e₂).unop.map_val, (IsFiltered.rightToMax e₁ e₂).unop.map_val⟩

/-- The linearity of the identification, on the germs at one neighbourhood. -/
theorem pointStalkCotangentAddIso_smul_germ (W : C) (z : Φ.fiber.obj W) (β : B.obj.obj (op W))
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
      (sectionsAlgebra J f (op W))).X n) :
    (pointStalkCotangentAddIso J Φ f n).hom
        ((Φ.toPresheafFiber W z B.obj).hom β • pointCotangentGerm J Φ f n W z s) =
      (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (pointStalkAlgebra J Φ f)).X n from
        (show pointStalkAlgebra J Φ f from (Φ.toPresheafFiber W z B.obj).hom β) •
          (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
            (pointStalkAlgebra J Φ f)).X n from
              (pointStalkCotangentAddIso J Φ f n).hom (pointCotangentGerm J Φ f n W z s))) := by
  have h₁ : (Φ.toPresheafFiber W z B.obj).hom β • pointCotangentGerm J Φ f n W z s =
      pointCotangentGerm J Φ f n W z
        (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (sectionsAlgebra J f (op W))).X n from (show sectionsAlgebra J f (op W) from β) • s) :=
    (smul_toPresheafModuleFiber J Φ ((cotangentComplex J f).X n) W z β _).trans
      (congrArg (Stacks.toPresheafModuleFiber Φ ((cotangentComplex J f).X n).val W z)
        (((sectionsCotangentComplexComparison J f (op W)).f n).hom.map_smul β s).symm)
  rw [h₁, pointStalkCotangentAddIso_germ, pointStalkCotangentAddIso_germ]
  exact cotangentComplexAbMap_pointGermSquare_smul J Φ f n W z β s

/-- **The identification is `B_Φ`-linear.** -/
theorem pointStalkCotangentAddIso_smul (b : (Φ.presheafFiber (A := CommRingCat)).obj B.obj)
    (m : (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J f).X n)) :
    (pointStalkCotangentAddIso J Φ f n).hom (b • m) =
      (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (pointStalkAlgebra J Φ f)).X n from
        (show pointStalkAlgebra J Φ f from b) •
          (show (CommAlgCat.cotangentComplex.{max u v w, max u v w} _
            (pointStalkAlgebra J Φ f)).X n from (pointStalkCotangentAddIso J Φ f n).hom m)) := by
  obtain ⟨U, x, s, rfl⟩ := exists_pointCotangentGerm_eq J Φ f n m
  obtain ⟨U', x', β, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := B.obj) b
  obtain ⟨W, z, g, g', rfl, rfl⟩ := exists_common_neighbourhood J Φ x x'
  rw [pointCotangentGerm_restrict J Φ f n g z s, ← Φ.toPresheafFiber_w_apply g' z B.obj β]
  exact pointStalkCotangentAddIso_smul_germ J Φ f n W z _ _

/-- The identification of the stalk at `Φ` of `L^n_{B/A}` with `L^n_{B_Φ/A_Φ}`, as an isomorphism
of `B_Φ`-modules. -/
def pointStalkCotangentLinearEquiv :
    (Stacks.sheafModuleFiberOfCommRing Φ B).obj ((cotangentComplex J f).X n) ≃ₗ[
      (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj B.obj]
      (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).X n :=
  { (pointStalkCotangentAddIso J Φ f n).addCommGroupIsoToAddEquiv with
    map_smul' := pointStalkCotangentAddIso_smul J Φ f n }

/-- On the germs at a neighbourhood `(U, x)`, `CategoryTheory.Sheaf.pointStalkCotangentLinearEquiv`
is the map induced by the germ square of `(U, x)`. -/
theorem pointStalkCotangentLinearEquiv_germ (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    pointStalkCotangentLinearEquiv J Φ f n (pointCotangentGerm J Φ f n U x s) =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s :=
  pointStalkCotangentAddIso_germ J Φ f n U x s

end Stalk

section Complex

attribute [local instance] moduleOfSections

/-- The stalk functor carries the differential of `L_{B/A}` on the germ of a sectionwise class
to the germ of its differential. -/
theorem sheafModuleFiberOfCommRing_map_d_germ (i j : ℤ) (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X i) :
    (Stacks.sheafModuleFiberOfCommRing Φ B).map ((cotangentComplex J f).d i j)
        (pointCotangentGerm J Φ f i U x s) =
      pointCotangentGerm J Φ f j U x
        ((CommAlgCat.cotangentComplex.{max u v w, max u v w} _
          (sectionsAlgebra J f (op U))).d i j s) :=
  (Stacks.toPresheafModuleFiber_naturality Φ ((cotangentComplex J f).d i j).val U x _).trans
    (congrArg (Stacks.toPresheafModuleFiber Φ ((cotangentComplex J f).X j).val U x)
      (ConcreteCategory.congr_hom ((sectionsCotangentComplexComparison J f (op U)).comm i j) s))

/-- **The stalk of the cotangent complex at a point of a site** (Tag 08T0): the stalk at `Φ` of
`L_{B/A}` is `L_{B_Φ/A_Φ}`, as complexes of `B_Φ`-modules. On germs it is described by
`CategoryTheory.Sheaf.pointStalkCotangentComplexIso_hom_germ`. -/
@[stacks 08T0 "The point is a point of the site in the sense of Stacks 00Y5 (Mathlib's
GrothendieckTopology.Point), with fibre functor valued in the universe of the sections of A and
B, the single universe of sets of the source. The left-hand side is the stalk at the point of
L_{B/A} as a complex of B_p-modules (Stacks.sheafModuleFiberOfCommRing), the right-hand side is
the cotangent complex of Tag 08PN of the ring map of stalks A_p -> B_p (pointStalkAlgebra). The
instance LocallySmall.{max u v w} C holds for every category C in these universes (Mathlib's
instance locallySmall_of_univLE), so it restricts nothing. On germs the isomorphism is described by
pointStalkCotangentComplexIso_hom_germ."]
def pointStalkCotangentComplexIso :
    ((Stacks.sheafModuleFiberOfCommRing Φ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex J f) ≅
      CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (pointStalkCotangentLinearEquiv J Φ f n).toModuleIso) (fun i j _ => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      obtain ⟨U, x, s, rfl⟩ := exists_pointCotangentGerm_eq J Φ f i m
      change (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f)).d i j
          (pointStalkCotangentLinearEquiv J Φ f i (pointCotangentGerm J Φ f i U x s)) =
        pointStalkCotangentLinearEquiv J Φ f j ((Stacks.sheafModuleFiberOfCommRing Φ B).map
          ((cotangentComplex J f).d i j) (pointCotangentGerm J Φ f i U x s))
      rw [sheafModuleFiberOfCommRing_map_d_germ, pointStalkCotangentLinearEquiv_germ,
        pointStalkCotangentLinearEquiv_germ]
      exact (ConcreteCategory.congr_hom
        ((CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).comm i j) s))

/-- **The stalk identification on germs.** The germ at a neighbourhood `(U, x)` of `Φ` of the
image of a class `s ∈ L^n_{B(U)/A(U)}` under the canonical map of Tag 08SX goes to the image of
`s` under the map of cotangent complexes induced by the germ maps `A(U) → A_Φ`, `B(U) → B_Φ`. -/
theorem pointStalkCotangentComplexIso_hom_germ (n : ℤ) (U : C) (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (pointStalkCotangentComplexIso J Φ f).hom.f n (pointCotangentGerm J Φ f n U x s) =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s :=
  pointStalkCotangentLinearEquiv_germ J Φ f n U x s

end Complex

/-! ## Naturality in commutative squares -/

section Naturality

attribute [local instance] moduleOfSections

variable {A' B' : Sheaf J CommRingCat.{max u v w}} {f' : A' ⟶ B'} (a : A ⟶ A') (b : B ⟶ B')
  (hsq : f ≫ b = a ≫ f')

/-- The commutative square of stalk maps `A_Φ → A'_Φ`, `B_Φ → B'_Φ` induced by a commutative
square of homomorphisms of sheaves of commutative rings. -/
def pointStalkSquare :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w}
      ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
      ((Φ.presheafFiber (A := CommRingCat)).obj A'.obj) (pointStalkAlgebra J Φ f)
      (pointStalkAlgebra J Φ f') where
  base := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom
  map := ((Φ.presheafFiber (A := CommRingCat)).map b.hom).hom
  map_algebraMap z := by
    change ((Φ.presheafFiber (A := CommRingCat)).map f.hom ≫
      (Φ.presheafFiber (A := CommRingCat)).map b.hom).hom z =
        ((Φ.presheafFiber (A := CommRingCat)).map a.hom ≫
          (Φ.presheafFiber (A := CommRingCat)).map f'.hom).hom z
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k : A ⟶ B' => ((Φ.presheafFiber (A := CommRingCat)).map k.hom).hom z) hsq

omit [LocallySmall.{max u v w} C] in
/-- The germ squares intertwine the square on sections over a neighbourhood with the square of
stalk maps. -/
theorem pointGermSquare_comp_pointStalkSquare (U : C) (x : Φ.fiber.obj U) :
    CommAlgCat.AlgebraSquare.comp.{max u v w, max u v w} (pointGermSquare J Φ f U x)
        (pointStalkSquare J Φ f a b hsq) =
      CommAlgCat.AlgebraSquare.comp.{max u v w, max u v w} (sectionsSquare J a b hsq (op U))
        (pointGermSquare J Φ f' U x) :=
  (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr
    ⟨congrArg CommRingCat.Hom.hom (Φ.toPresheafFiber_naturality a.hom U x),
      congrArg CommRingCat.Hom.hom (Φ.toPresheafFiber_naturality b.hom U x)⟩

omit [LocallySmall.{max u v w} C] in
/-- On the ring side, the map induced by a germ square followed by the map of stalk squares is
the map of the square on sections followed by the map of the germ square. -/
theorem cotangentComplexAbMap_pointGermSquare_pointStalkSquare (U : C) (x : Φ.fiber.obj U)
    (n : ℤ)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (CommAlgCat.cotangentComplexAbMap (pointStalkSquare J Φ f a b hsq)).f n
        ((CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f U x)).f n s) =
      (CommAlgCat.cotangentComplexAbMap (pointGermSquare J Φ f' U x)).f n
        ((CommAlgCat.cotangentComplexAbMap (sectionsSquare J a b hsq (op U))).f n s) := by
  have h := congrArg (fun k => HomologicalComplex.Hom.f k n)
    (((CommAlgCat.cotangentComplexAbMap_comp.{max u v w} _ _).symm.trans
      (congrArg CommAlgCat.cotangentComplexAbMap.{max u v w, max u v w, max u v w}
        (pointGermSquare_comp_pointStalkSquare J Φ f a b hsq U x))).trans
      (CommAlgCat.cotangentComplexAbMap_comp.{max u v w} _ _))
  exact ConcreteCategory.congr_hom h s

/-- **The stalk of the map of cotangent complexes of a square, on germs.** The stalk at `Φ` of
the map `L_{B/A} ⟶ L_{B'/A'}` of a commutative square carries the germ of the image of a
sectionwise class `s` to the germ of the image of the image of `s` under the map of the square
on sections. -/
theorem sheafModuleFiberOfCommRing_map_squareCotangentComplexMap_germ (n : ℤ) (U : C)
    (x : Φ.fiber.obj U)
    (s : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (sectionsAlgebra J f (op U))).X n) :
    (Stacks.sheafModuleFiberOfCommRing Φ B).map
        ((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)).f n)
        (pointCotangentGerm J Φ f n U x s) =
      Stacks.toPresheafModuleFiber Φ ((squareRestrict.{u, v, w} J b).obj
        ((cotangentComplex J f').X n)).val U x
        ((sectionsCotangentComplexComparison J f' (op U)).f n
          ((CommAlgCat.cotangentComplexAbMap (sectionsSquare J a b hsq (op U))).f n s)) :=
  (Stacks.toPresheafModuleFiber_naturality Φ
    ((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)).f n).val U x _).trans
    (congrArg (Stacks.toPresheafModuleFiber Φ ((squareRestrict.{u, v, w} J b).obj
        ((cotangentComplex J f').X n)).val U x)
      (sectionsCotangentComplexComparison_square J a b hsq (op U) n s))

end Naturality

end CategoryTheory.Sheaf

end
