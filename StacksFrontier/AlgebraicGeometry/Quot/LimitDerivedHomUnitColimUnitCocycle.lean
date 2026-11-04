module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence

/-!
# The cocycle of the identification `Lf^*𝒪_Y ≅ 𝒪_X`

For a pullback pseudofunctor datum `P`, a distinguished object of each fibre and identifications
of their inverse images, the cocycle condition says that the identification along a composite
`f ≫ g` is the composition comparison followed by the identifications along `g` and `f`. This
file shows that the cocycle condition is preserved by the constructions from which the derived
inverse image of the structure sheaf is built, and deduces the cocycle for
`AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` from the cocycle at the single
complex.

## Main definitions

* `CategoryTheory.PullbackData.singleUnitIso`: an identification of inverse images of
  distinguished objects, placed in degree zero.
* `AlgebraicGeometry.Space.toposUnitIso`: the identification `f^*𝒪_Y ≅ 𝒪_X` for the inverse image
  of modules along the morphism of small étale ringed topoi.

## Main results

* `CategoryTheory.PullbackData.transport_unit_comp`: the cocycle survives transporting a datum
  along isomorphisms of its inverse images.
* `CategoryTheory.PullbackData.singleUnitIso_comp`: the cocycle for the identifications placed in
  degree zero.
* `CategoryTheory.PullbackData.toHomotopy_unit_comp`: the cocycle on the homotopy categories.
* `CategoryTheory.PullbackData.leftDerived_unit_comp`: the cocycle for the left derived datum.
* `CategoryTheory.PullbackData.compIso_unit_comp_conj`: the cocycle survives conjugating the
  distinguished objects by isomorphisms.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso_hom` and
  `AlgebraicGeometry.Space.derivedPullbackCoherence_unitPullIso_hom`: the identifications
  `Lf^*𝒪_Y ≅ 𝒪_X` written out through the generic constructions.
* `AlgebraicGeometry.Space.unitPullIso_comp`: the cocycle for
  `AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso`, given the cocycle for
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso` as a hypothesis.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂ v₃ u₃

/-! ### The transport layer -/

section Transport

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]

/-- Conjugating the distinguished objects by isomorphisms preserves the cocycle. -/
private theorem compIso_unit_comp_conj_aux (P : PullbackData A M) {a b d : A} (f : a ⟶ b)
    (g : b ⟶ d)
    {Ta : M a} {Tb : M b} {Td : M d} {Ua : M a} {Ub : M b} {Ud : M d}
    (sa : Ta ≅ Ua) (sb : Tb ≅ Ub) (sd : Td ≅ Ud)
    (wf : (P.pull f).obj Ub ⟶ Ua) (wg : (P.pull g).obj Ud ⟶ Ub)
    (wk : (P.pull (f ≫ g)).obj Ud ⟶ Ua)
    (h : (P.compIso f g).hom.app Ud ≫ (P.pull f).map wg ≫ wf = wk) :
    (P.compIso f g).hom.app Td ≫
        (P.pull f).map ((P.pull g).map sd.hom ≫ wg ≫ sb.inv) ≫
          ((P.pull f).map sb.hom ≫ wf ≫ sa.inv) =
      (P.pull (f ≫ g)).map sd.hom ≫ wk ≫ sa.inv := by
  have n : (P.pull (f ≫ g)).map sd.hom ≫ (P.compIso f g).hom.app Ud =
      (P.compIso f g).hom.app Td ≫ (P.pull f).map ((P.pull g).map sd.hom) :=
    (P.compIso f g).hom.naturality sd.hom
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (P.pull f) sb.inv sb.hom, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp, ← reassoc_of% n, reassoc_of% h]

/-- The cocycle of an identification of inverse images of a distinguished object survives
transport along isomorphisms of the inverse images: the identifications transported from `P'`
satisfy the cocycle for `CategoryTheory.PullbackData.transport` as soon as the original ones
satisfy it for `P'`. -/
theorem transport_unit_comp (P' : PullbackData A M)
    (pull' : ∀ {a b : A}, (a ⟶ b) → (M b ⥤ M a))
    (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P'.pull f)
    {a b d : A} (f : a ⟶ b) (g : b ⟶ d) {Oa : M a} {Ob : M b} {Od : M d}
    (mf : (P'.pull f).obj Ob ≅ Oa) (mg : (P'.pull g).obj Od ≅ Ob)
    (mk : (P'.pull (f ≫ g)).obj Od ≅ Oa)
    (h : (P'.compIso f g).hom.app Od ≫ (P'.pull f).map mg.hom ≫ mf.hom = mk.hom) :
    ((transport P' pull' ε).compIso f g).hom.app Od ≫
        ((transport P' pull' ε).pull f).map ((ε g).app Od ≪≫ mg).hom ≫
          ((ε f).app Ob ≪≫ mf).hom =
      ((ε (f ≫ g)).app Od ≪≫ mk).hom := by
  show ((transport P' pull' ε).compIso f g).hom.app Od ≫
      ((transport P' pull' ε).pull f).map ((ε g).hom.app Od ≫ mg.hom) ≫
        ((ε f).hom.app Ob ≫ mf.hom) =
    (ε (f ≫ g)).hom.app Od ≫ mk.hom
  have n := (ε f).inv.naturality ((ε g).hom.app Od ≫ mg.hom)
  simp only [transport, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← reassoc_of% n, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app_assoc, h]

end Transport

/-! ### The single-complex layer -/

section Single

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Preadditive (M a)] [∀ a, HasZeroObject (M a)]

/-- An identification `f^*O ≅ O'` of inverse images of distinguished objects, placed in degree
zero: the inverse image of the complex concentrated in degree zero on `O` is identified with the
complex concentrated in degree zero on `O'`. -/
def singleUnitIso (P : PullbackData A M) [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
    {a b : A} (f : a ⟶ b) {Ob : M b} {Oa : M a} (uf : (P.pull f).obj Ob ≅ Oa) :
    ((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj Ob) ≅
      (HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).obj Oa :=
  (HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).app Ob ≪≫
    (HomologicalComplex.single (M a) (ComplexShape.up ℤ) 0).mapIso uf

/-- In degree zero, the hom of `singleUnitIso P f uf` is the inverse image of the degree-zero
identification of `single 0 Ob`, followed by `uf.hom` and the degree-zero identification of
`single 0 Oa`. -/
theorem singleUnitIso_hom_f_zero (P : PullbackData A M)
    [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
    {a b : A} (f : a ⟶ b) {Ob : M b} {Oa : M a} (uf : (P.pull f).obj Ob ≅ Oa) :
    (singleUnitIso P f uf).hom.f 0 =
      (P.pull f).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Ob).hom ≫
        uf.hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Oa).inv := by
  simp [singleUnitIso, HomologicalComplex.single_map_f_self]

/-- An identification of inverse images of distinguished objects satisfying the cocycle for `P`
gives identifications of the complexes concentrated in degree zero satisfying the cocycle for the
inverse images of complexes. -/
theorem singleUnitIso_comp (P : PullbackData A M)
    [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
    {a b d : A} (f : a ⟶ b) (g : b ⟶ d) {Oa : M a} {Ob : M b} {Od : M d}
    (uf : (P.pull f).obj Ob ≅ Oa) (ug : (P.pull g).obj Od ≅ Ob)
    (uk : (P.pull (f ≫ g)).obj Od ≅ Oa)
    (h : (P.compIso f g).hom.app Od ≫ (P.pull f).map ug.hom ≫ uf.hom = uk.hom) :
    ((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).map (singleUnitIso P g ug).hom ≫
        (singleUnitIso P f uf).hom =
      (NatTrans.mapHomologicalComplex (P.compIso f g).inv (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od) ≫
        (singleUnitIso P (f ≫ g) uk).hom := by
  refine HomologicalComplex.to_single_hom_ext (j := 0) ?_
  have := compIso_unit_comp_conj_aux P f g
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) Oa)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) Ob)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) Od) uf.hom ug.hom uk.hom h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, singleUnitIso_hom_f_zero, Functor.map_comp,
    Category.assoc]
  rw [← cancel_epi ((P.compIso f g).hom.app _), Iso.hom_inv_id_app_assoc]
  simpa using this

end Single

/-! ### The homotopy layer -/

section Homotopy

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Preadditive (M a)] [∀ a, HasZeroObject (M a)]

/-- An identification of inverse images of distinguished objects satisfying the cocycle for `P`
gives identifications of the complexes concentrated in degree zero, in the homotopy categories,
satisfying the cocycle for `CategoryTheory.PullbackData.toHomotopy`. -/
theorem toHomotopy_unit_comp (P : PullbackData A M)
    [hadd : ∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
    {a b d : A} (f : a ⟶ b) (g : b ⟶ d) {Oa : M a} {Ob : M b} {Od : M d}
    (uf : (P.pull f).obj Ob ≅ Oa) (ug : (P.pull g).obj Od ≅ Ob)
    (uk : (P.pull (f ≫ g)).obj Od ≅ Oa)
    (h : (P.compIso f g).hom.app Od ≫ (P.pull f).map ug.hom ≫ uf.hom = uk.hom) :
    ((toHomotopy P).pull f).map ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          (singleUnitIso P g ug).hom) ≫
        (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map (singleUnitIso P f uf).hom =
      ((toHomotopy P).compIso f g).inv.app
          ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) ≫
        (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
          (singleUnitIso P (f ≫ g) uk).hom := by
  show ((P.pull f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).map
          (singleUnitIso P g ug).hom) ≫
      (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map (singleUnitIso P f uf).hom =
    ((toHomotopy P).compIso f g).inv.app
        ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) ≫
      (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        (singleUnitIso P (f ≫ g) uk).hom
  have hc : ((toHomotopy P).compIso f g).inv.app
      ((HomotopyCategory.quotient (M d) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) =
      (HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (P.compIso f g).inv (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)) := by
    have := toHomotopy_triangle_inv_app P (f := f) (g := g) rfl
      ((HomologicalComplex.single (M d) (ComplexShape.up ℤ) 0).obj Od)
    rwa [triangle_rfl, triangle_rfl] at this
  rw [hc, Functor.mapHomotopyCategory_map]
  refine Eq.trans ?_ ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map_comp _ _)
  refine Eq.trans ((HomotopyCategory.quotient (M a) (ComplexShape.up ℤ)).map_comp _ _).symm ?_
  exact congrArg _ (singleUnitIso_comp P f g uf ug uk h)

end Homotopy

/-! ### The derived layer -/

section Derived

variable {A : Type u₁} [Category.{v₁} A] {H : A → Type u₂} [∀ a, Category.{v₂} (H a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)]
  (Q : ∀ a, H a ⥤ D a) (W : ∀ a, MorphismProperty (H a)) [∀ a, (Q a).IsLocalization (W a)]
  (P : PullbackData A H) (L : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
  (c : ∀ {a b : A} (f : a ⟶ b), Q b ⋙ L f ⟶ P.pull f ⋙ Q a)
  [hL : ∀ {a b : A} (f : a ⟶ b), (L f).IsLeftDerivedFunctor (c f) (W b)]
  [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), IsIso (derivedComp Q W P L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift Q W P L c a)]

/-- Morphisms `f^*K_b ⟶ K_a` of underived inverse images satisfying the cocycle for `P` give,
composed with the comparisons `c` from the derived to the underived inverse images, morphisms of
derived inverse images satisfying the cocycle for `CategoryTheory.PullbackData.leftDerived`. -/
theorem leftDerived_unit_comp {a b d : A} (f : a ⟶ b) (g : b ⟶ d)
    {Ka : H a} {Kb : H b} {Kd : H d}
    (vf : (P.pull f).obj Kb ⟶ Ka) (vg : (P.pull g).obj Kd ⟶ Kb)
    (vk : (P.pull (f ≫ g)).obj Kd ⟶ Ka)
    (h : (P.pull f).map vg ≫ vf = (P.compIso f g).inv.app Kd ≫ vk) :
    ((leftDerived Q W P L c).compIso f g).hom.app ((Q d).obj Kd) ≫
        (L f).map ((c g).app Kd ≫ (Q b).map vg) ≫ (c f).app Kb ≫ (Q a).map vf =
      (c (f ≫ g)).app Kd ≫ (Q a).map vk := by
  have hinv : ((leftDerived Q W P L c).compIso f g).inv.app ((Q d).obj Kd) =
      (derivedComp Q W P L c f g).app ((Q d).obj Kd) := rfl
  rw [← cancel_epi (((leftDerived Q W P L c).compIso f g).inv.app ((Q d).obj Kd)),
    Iso.inv_hom_id_app_assoc, hinv, derivedComp_fac_assoc]
  have n := (c f).naturality vg
  dsimp at n
  have hq : (Q a).map ((P.pull f).map vg) ≫ (Q a).map vf =
      (Q a).map ((P.compIso f g).inv.app Kd) ≫ (Q a).map vk :=
    ((Q a).map_comp _ _).symm.trans ((congrArg (Q a).map h).trans ((Q a).map_comp _ _))
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n, hq]

end Derived

/-! ### Conjugating the distinguished objects -/

section Conjugate

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]

/-- The cocycle of morphisms of inverse images of distinguished objects survives conjugating the
distinguished objects by isomorphisms `sa`, `sb`, `sd`. -/
theorem compIso_unit_comp_conj (P : PullbackData A D) {a b d : A} (f : a ⟶ b) (g : b ⟶ d)
    {Ta : D a} {Tb : D b} {Td : D d} {Ua : D a} {Ub : D b} {Ud : D d}
    (sa : Ta ≅ Ua) (sb : Tb ≅ Ub) (sd : Td ≅ Ud)
    (wf : (P.pull f).obj Ub ⟶ Ua) (wg : (P.pull g).obj Ud ⟶ Ub)
    (wk : (P.pull (f ≫ g)).obj Ud ⟶ Ua)
    (h : (P.compIso f g).hom.app Ud ≫ (P.pull f).map wg ≫ wf = wk) :
    (P.compIso f g).hom.app Td ≫
        (P.pull f).map ((P.pull g).map sd.hom ≫ wg ≫ sb.inv) ≫
          ((P.pull f).map sb.hom ≫ wf ≫ sa.inv) =
      (P.pull (f ≫ g)).map sd.hom ≫ wk ≫ sa.inv :=
  compIso_unit_comp_conj_aux P f g sa sb sd wf wg wk h

end Conjugate

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identification `f^*𝒪_Y ≅ 𝒪_X` for the inverse image of modules along the morphism of
small étale ringed topoi. -/
abbrev toposUnitIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((toposPullbackData B S hS).pull f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  (toposPullbackModulesIso f).app (SheafOfModules.unit (structureRingSheaf B S hS Y)) ≪≫
    modulePullbackUnitIso B S hS f

variable {B S hS}

/-- The identification `Lf^*𝒪_Y ≅ 𝒪_X` of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso`, written through the generic
identification of degree zero. -/
theorem smallEtaleDerivedPullbackUnitComplexIso_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleDerivedPullbackUnitComplexIso f).hom =
      (smallEtaleDerivedModulePullbackComparison B S hS f).app (unitComplex Y) ≫
        (toposQh X).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (PullbackData.singleUnitIso (toposPullbackData B S hS) f (toposUnitIso B S hS f)).hom) :=
  rfl

/-- `AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` of
`AlgebraicGeometry.Space.derivedPullbackCoherence` is the identification at the single complex,
conjugated by the identification of the single functor on the derived category with the single
functor on the homotopy category followed by the localization. -/
theorem derivedPullbackCoherence_unitPullIso_hom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((derivedPullbackCoherence B S hS).unitPullIso f).hom =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((DerivedCategory.singleFunctorIsoCompQh (toposModules B S hS Y) 0).hom.app
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) ≫
        (smallEtaleDerivedPullbackUnitComplexIso f).hom ≫
          (DerivedCategory.singleFunctorIsoCompQh (toposModules B S hS X) 0).inv.app
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) :=
  rfl

/-- The cocycle of `AlgebraicGeometry.Space.DerivedPullbackCoherence.unitPullIso` for
`AlgebraicGeometry.Space.derivedPullbackCoherence`, given as hypothesis `hsingle` the same cocycle
for `AlgebraicGeometry.Space.smallEtaleDerivedPullbackUnitComplexIso`: for `f : X ⟶ Y` and
`g : Y ⟶ Z`, the identification of `L(f ≫ g)^*𝒪_Z` with `𝒪_X` is the composition comparison,
followed by the identification for `g` pushed forward by `Lf^*`, followed by the identification
for `f`. -/
theorem unitPullIso_comp
    (hsingle : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      ((derivedPullbackCoherence B S hS).compIso f g).hom.app
            ((toposQh Z).obj (unitComplex Z)) ≫
          (smallEtaleDerivedModulePullback B S hS f).map
            (smallEtaleDerivedPullbackUnitComplexIso g).hom ≫
          (smallEtaleDerivedPullbackUnitComplexIso f).hom =
        (smallEtaleDerivedPullbackUnitComplexIso (f ≫ g)).hom)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((derivedPullbackCoherence B S hS).compIso f g).hom.app (structureObject B S hS Z) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          ((derivedPullbackCoherence B S hS).unitPullIso g).hom ≫
        ((derivedPullbackCoherence B S hS).unitPullIso f).hom =
      ((derivedPullbackCoherence B S hS).unitPullIso (f ≫ g)).hom := by
  rw [derivedPullbackCoherence_unitPullIso_hom, derivedPullbackCoherence_unitPullIso_hom,
    derivedPullbackCoherence_unitPullIso_hom]
  exact PullbackData.compIso_unit_comp_conj (toposDerivedPullbackData B S hS) f g
    ((DerivedCategory.singleFunctorIsoCompQh (toposModules B S hS X) 0).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))
    ((DerivedCategory.singleFunctorIsoCompQh (toposModules B S hS Y) 0).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)))
    ((DerivedCategory.singleFunctorIsoCompQh (toposModules B S hS Z) 0).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)))
    _ _ _ (hsingle f g)

end AlgebraicGeometry.Space

end
