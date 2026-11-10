module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisGlobalSectionsPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Galois sections of a pairing act on the base change

Let `p : T ⟶ Z` be a morphism of schemes and `b : G₁ × G₂ ⟶ G₃` a section-wise pairing of
sheaves of modules on `Z_étale` (`Stacks.EtaleCohomology.EtaleSectionPairing`). A section `s` of
`G₂` over an étale `Z`-scheme `W`, together with a lift `r : T ⟶ W` of `p`, defines a morphism of
sheaves of abelian groups `p⁻¹G₁ ⟶ p⁻¹G₃` on `T_étale`
(`Stacks.EtaleCohomology.sectionPairingAct`): on a section `a` of `G₁` over `U`, pair `a` and `s`
over `U ×_Z W` and pull back along `(id, r) : U ×_Z T ⟶ (U ×_Z W) ×_Z T`. It is the transpose, for
`p⁻¹ ⊣ p_*`, of the morphism `G₁ ⟶ p_*p⁻¹G₃` doing this
(`Stacks.EtaleCohomology.sectionPairingPushforwardMap`); it is `ℤ`-linear, so it is built after
restricting scalars to `ℤ`.

For `T = Y_K` the base change of a `k`-scheme `Y` to a separable algebraic extension `K/k` and
`W = Y_E` a finite stage, every global section `e` of `G₂|_{Y_K}` comes from such a stage, and the
morphism only depends on `e` (`Stacks.EtaleCohomology.galoisSectionAct`). On global sections it is
the Galois pairing with `e` (`Stacks.EtaleCohomology.galoisGlobalSectionsPairing`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Fiber

variable {Z : Scheme.{u}} (U W : Z.Etale)

/-- **The fibre product `U ×_Z W` of two étale `Z`-schemes**, as an étale `Z`-scheme. -/
def etaleFiberObj : Z.Etale := Scheme.Etale.mk (pullback.fst U.hom W.hom ≫ U.hom)

/-- The first projection `U ×_Z W ⟶ U`. -/
def etaleFiberFst : etaleFiberObj U W ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom W.hom) rfl trivial

/-- The second projection `U ×_Z W ⟶ W`. -/
def etaleFiberSnd : etaleFiberObj U W ⟶ W :=
  MorphismProperty.Over.homMk (pullback.snd U.hom W.hom) pullback.condition.symm trivial

variable {U} in
/-- The fibre product is functorial in its first factor. -/
def etaleFiberMap {V : Z.Etale} (φ : V ⟶ U) : etaleFiberObj V W ⟶ etaleFiberObj U W :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst V.hom W.hom ≫ φ.left) (pullback.snd V.hom W.hom)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst V.hom W.hom ≫ ·)
        (MorphismProperty.Over.w φ)).trans pullback.condition)))
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom) (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).trans (congrArg (pullback.fst V.hom W.hom ≫ ·)
        (MorphismProperty.Over.w φ))))) trivial

variable {U} in
/-- The first projection intertwines `etaleFiberMap W φ` with `φ`. -/
lemma etaleFiberMap_fst {V : Z.Etale} (φ : V ⟶ U) :
    etaleFiberMap W φ ≫ etaleFiberFst U W = etaleFiberFst V W ≫ φ :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

variable {U} in
/-- `etaleFiberMap W φ` commutes with the second projections. -/
lemma etaleFiberMap_snd {V : Z.Etale} (φ : V ⟶ U) :
    etaleFiberMap W φ ≫ etaleFiberSnd U W = etaleFiberSnd V W :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

variable {U} in
/-- The section `(id, t) : U ⟶ U ×_Z W` of the first projection, for `t : U ⟶ W`. -/
def etaleFiberSection (t : U ⟶ W) : U ⟶ etaleFiberObj U W :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 U.left) t.left
      ((Category.id_comp _).trans (MorphismProperty.Over.w t).symm))
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom) (pullback.lift_fst _ _ _)).trans
      (Category.id_comp _))) trivial

variable {U} in
/-- The section `(id, t)` is a section of the first projection. -/
lemma etaleFiberSection_fst (t : U ⟶ W) : etaleFiberSection W t ≫ etaleFiberFst U W = 𝟙 U :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

variable {U} in
/-- The second component of the section `(id, t)` is `t`. -/
lemma etaleFiberSection_snd (t : U ⟶ W) : etaleFiberSection W t ≫ etaleFiberSnd U W = t :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

variable {W} in
/-- The fibre product is functorial in its second factor. -/
def etaleFiberMapRight {W' : Z.Etale} (t : W' ⟶ W) : etaleFiberObj U W' ⟶ etaleFiberObj U W :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst U.hom W'.hom) (pullback.snd U.hom W'.hom ≫ t.left)
      (pullback.condition.trans ((congrArg (pullback.snd U.hom W'.hom ≫ ·)
        (MorphismProperty.Over.w t).symm).trans (Category.assoc _ _ _).symm)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (pullback.lift_fst _ _ _))) trivial

variable {W} in
/-- `etaleFiberMapRight U t` commutes with the first projections. -/
lemma etaleFiberMapRight_fst {W' : Z.Etale} (t : W' ⟶ W) :
    etaleFiberMapRight U t ≫ etaleFiberFst U W = etaleFiberFst U W' :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

variable {W} in
/-- The second projection intertwines `etaleFiberMapRight U t` with `t`. -/
lemma etaleFiberMapRight_snd {W' : Z.Etale} (t : W' ⟶ W) :
    etaleFiberMapRight U t ≫ etaleFiberSnd U W = etaleFiberSnd U W' ≫ t :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

variable {U W} {T : Scheme.{u}} (p : T ⟶ Z)

/-- A morphism into a base change, from a morphism into the étale scheme lying over `p`. -/
def etaleBaseChangeHomMk {A : T.Etale} {V : Z.Etale} (g : A.left ⟶ V.left)
    (hg : g ≫ V.hom = A.hom ≫ p) : A ⟶ (smallEtaleBaseChange p).obj V :=
  MorphismProperty.Over.homMk (pullback.lift g A.hom hg) (by exact pullback.lift_snd _ _ _) trivial

/-- The first component of `etaleBaseChangeHomMk p g hg` is `g`. -/
lemma etaleBaseChangeHomMk_left_fst {A : T.Etale} {V : Z.Etale} (g : A.left ⟶ V.left)
    (hg : g ≫ V.hom = A.hom ≫ p) :
    (etaleBaseChangeHomMk p g hg).left ≫ pullback.fst V.hom p = g :=
  pullback.lift_fst _ _ _

variable (U) {r : T ⟶ W.left} (hr : r ≫ W.hom = p)

include hr in
/-- The composites `U ×_Z T ⟶ U ⟶ Z` and `U ×_Z T ⟶ T ⟶ W ⟶ Z`, the latter through `r`, agree
when `r ≫ W.hom = p`. -/
lemma etaleFiberLift_aux :
    pullback.fst U.hom p ≫ U.hom = (pullback.snd U.hom p ≫ r) ≫ W.hom :=
  pullback.condition.trans ((congrArg (pullback.snd U.hom p ≫ ·) hr.symm).trans
    (Category.assoc _ _ _).symm)

/-- **The morphism `(id, r) : U ×_Z T ⟶ (U ×_Z W) ×_Z T`** of étale `T`-schemes, for a lift
`r : T ⟶ W` of `p`. -/
def etaleFiberLift :
    (smallEtaleBaseChange p).obj U ⟶ (smallEtaleBaseChange p).obj (etaleFiberObj U W) :=
  etaleBaseChangeHomMk p
    (pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r) (etaleFiberLift_aux U p hr))
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.hom) (pullback.lift_fst _ _ _)).trans
      pullback.condition))

/-- For `m : V ×_Z T ⟶ U ×_Z T` lying over `φ` and over `T`, the composite of `m` with
`(pr₁, r ∘ pr₂) : U ×_Z T ⟶ U ×_Z W` is `(pr₁, r ∘ pr₂) : V ×_Z T ⟶ V ×_Z W` followed by
`φ ×_Z W`. -/
lemma etaleFiberLift_naturality_aux {V : Z.Etale} (φ : V ⟶ U)
    (m : pullback V.hom p ⟶ pullback U.hom p)
    (hm₁ : m ≫ pullback.fst U.hom p = pullback.fst V.hom p ≫ φ.left)
    (hm₂ : m ≫ pullback.snd U.hom p = pullback.snd V.hom p) :
    m ≫ pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r)
        (etaleFiberLift_aux U p hr) =
      pullback.lift (pullback.fst V.hom p) (pullback.snd V.hom p ≫ r)
          (etaleFiberLift_aux V p hr) ≫
        pullback.lift (pullback.fst V.hom W.hom ≫ φ.left) (pullback.snd V.hom W.hom)
          ((Category.assoc _ _ _).trans ((congrArg (pullback.fst V.hom W.hom ≫ ·)
            (MorphismProperty.Over.w φ)).trans pullback.condition)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hm₁, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd,
      ← Category.assoc, hm₂]

include hr in
/-- The lifts are compatible with the functoriality of the fibre product. -/
lemma etaleFiberLift_naturality {V : Z.Etale} (φ : V ⟶ U) :
    etaleFiberLift V p hr ≫ (smallEtaleBaseChange p).map (etaleFiberMap W φ) =
      (smallEtaleBaseChange p).map φ ≫ etaleFiberLift U p hr := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (etaleBaseChangeHomMk_left_fst _ _ _))).trans ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (etaleBaseChangeHomMk_left_fst _ _ _))).symm
  exact (etaleFiberLift_naturality_aux U p hr φ _ (smallEtaleBaseChange_map_left_fst _ _)
    (smallEtaleBaseChange_w p ((smallEtaleBaseChange p).map φ))).symm

/-- For `m : T ⟶ U ×_Z T` with components `r'` and `𝟙 T`, the composite of `m` with
`(pr₁, r ∘ pr₂) : U ×_Z T ⟶ U ×_Z W` is `r'` followed by `(id, t) : U ⟶ U ×_Z W`, when
`r = t ∘ r'`. -/
lemma smallEtaleBaseChangeLift_comp_etaleFiberLift_aux (t : U ⟶ W) {r' : T ⟶ U.left}
    (hrt : r' ≫ t.left = r) (m : T ⟶ pullback U.hom p) (hm₁ : m ≫ pullback.fst U.hom p = r')
    (hm₂ : m ≫ pullback.snd U.hom p = 𝟙 T) :
    m ≫ pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r)
        (etaleFiberLift_aux U p hr) =
      r' ≫ pullback.lift (𝟙 U.left) t.left
        ((Category.id_comp _).trans (MorphismProperty.Over.w t).symm) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hm₁, Category.assoc, pullback.lift_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hm₂, Category.id_comp,
      Category.assoc, pullback.lift_snd, hrt]

/-- **Pulling back from `U` along `r'` and then lifting to the fibre product** is pulling back
from `U ×_Z W` along `(id, t) ∘ r'`, when `r = t ∘ r'`. -/
lemma smallEtaleBaseChangeLift_comp_etaleFiberLift (t : U ⟶ W) {r' : T ⟶ U.left}
    (hr' : r' ≫ U.hom = p) (hrt : r' ≫ t.left = r) :
    smallEtaleBaseChangeLift p U r' hr' ≫ etaleFiberLift U p hr =
      smallEtaleBaseChangeLift p (etaleFiberObj U W) (r' ≫ (etaleFiberSection W t).left)
        ((Category.assoc _ _ _).trans ((congrArg (r' ≫ ·)
          (MorphismProperty.Over.w (etaleFiberSection W t))).trans hr')) := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (etaleBaseChangeHomMk_left_fst _ _ _)).trans ?_)
  refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
  exact smallEtaleBaseChangeLift_comp_etaleFiberLift_aux U p hr t hrt _
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The first component of `etaleFiberLift U p hr` is the morphism
`(pr₁, r ∘ pr₂) : U ×_Z T ⟶ U ×_Z W`. -/
lemma etaleFiberLift_left_fst :
    (etaleFiberLift U p hr).left ≫ pullback.fst (etaleFiberObj U W).hom p =
      pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r)
        (etaleFiberLift_aux U p hr) :=
  etaleBaseChangeHomMk_left_fst _ _ _

/-- The morphism `(pr₁, r' ∘ pr₂) : U ×_Z T ⟶ U ×_Z W'` followed by `U ×_Z t` is
`(pr₁, r ∘ pr₂) : U ×_Z T ⟶ U ×_Z W`, when `r = t ∘ r'`. -/
lemma etaleFiberLift_mapRight_aux {W' : Z.Etale} (t : W' ⟶ W) {r' : T ⟶ W'.left}
    (hr' : r' ≫ W'.hom = p) (hrt : r' ≫ t.left = r) :
    pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r') (etaleFiberLift_aux U p hr') ≫
        pullback.lift (pullback.fst U.hom W'.hom) (pullback.snd U.hom W'.hom ≫ t.left)
          (pullback.condition.trans ((congrArg (pullback.snd U.hom W'.hom ≫ ·)
            (MorphismProperty.Over.w t).symm).trans (Category.assoc _ _ _).symm)) =
      pullback.lift (pullback.fst U.hom p) (pullback.snd U.hom p ≫ r)
        (etaleFiberLift_aux U p hr) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, hrt,
      pullback.lift_snd]

/-- The lifts are compatible with the functoriality of the fibre product in its second factor. -/
lemma etaleFiberLift_mapRight {W' : Z.Etale} (t : W' ⟶ W) {r' : T ⟶ W'.left}
    (hr' : r' ≫ W'.hom = p) (hrt : r' ≫ t.left = r) :
    etaleFiberLift U p hr' ≫ (smallEtaleBaseChange p).map (etaleFiberMapRight U t) =
      etaleFiberLift U p hr := by
  apply smallEtaleBaseChange_hom_ext
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (etaleBaseChangeHomMk_left_fst _ _ _))).trans ?_
  exact (etaleFiberLift_mapRight_aux U p hr t hr' hrt).trans
    (etaleFiberLift_left_fst U p hr).symm

end Fiber

section Act

variable {Z T : Scheme.{u}} (p : T ⟶ Z) {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃]
  {G₁ : EtaleModules.{u, 0} Λ₁ Z} {G₂ : EtaleModules.{u, 0} Λ₂ Z} {G₃ : EtaleModules.{u, 0} Λ₃ Z}
  (b : EtaleSectionPairing G₁ G₂ G₃) {W : Z.Etale} {r : T ⟶ W.left} (hr : r ≫ W.hom = p)
  (s : G₂.obj.obj (op W))

/-- An additive map between modules over two rings is `ℤ`-linear for the restricted
structures. -/
def restrictScalarsIntOfAddHom {A : ModuleCat.{u + 1} Λ₁} {B : ModuleCat.{u + 1} Λ₃}
    (f : A →+ B) :
    (ModuleCat.restrictScalars (Int.castRingHom Λ₁)).obj A ⟶
      (ModuleCat.restrictScalars (Int.castRingHom Λ₃)).obj B :=
  letI : Module ℤ A := Module.compHom A (Int.castRingHom Λ₁)
  letI : Module ℤ B := Module.compHom B (Int.castRingHom Λ₃)
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun z x => by
        change f ((Int.castRingHom Λ₁ z) • x) = (Int.castRingHom Λ₃ z) • f x
        rw [eq_intCast, eq_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul] }

/-- The section-wise value of `Stacks.EtaleCohomology.sectionPairingPushforwardMap`: a section
`a` of `G₁` over `U` goes to `b(a, s)` over `U ×_Z W`, pulled back along `(id, r)`. -/
def sectionPairingPushforwardFun (U : Z.Etaleᵒᵖ) :
    G₁.obj.obj U →+ ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.obj
      (op ((smallEtaleBaseChange p).obj U.unop)) :=
  ((((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.map
      (etaleFiberLift U.unop p hr).op).hom.toAddMonoidHom.comp
    (((etaleModuleInverseImageAdj.{u, 0} Λ₃ p).unit.app G₃).hom.app
      (op (etaleFiberObj U.unop W))).hom.toAddMonoidHom).comp
    (((b.app (op (etaleFiberObj U.unop W))).flip
      (G₂.obj.map (etaleFiberSnd U.unop W).op s)).comp
      (G₁.obj.map (etaleFiberFst U.unop W).op).hom.toAddMonoidHom)

/-- The value of `sectionPairingPushforwardFun` on a section `a`: the pullback along `(id, r)`
of the unit image of `b(a, s)` over `U ×_Z W`. -/
lemma sectionPairingPushforwardFun_apply (U : Z.Etaleᵒᵖ) (a : G₁.obj.obj U) :
    sectionPairingPushforwardFun p b hr s U a =
      ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.map (etaleFiberLift U.unop p hr).op
        (moduleUnitSection Λ₃ p G₃ (b.app (op (etaleFiberObj U.unop W))
          (G₁.obj.map (etaleFiberFst U.unop W).op a) (G₂.obj.map (etaleFiberSnd U.unop W).op s))) :=
  rfl

/-- Pulling back sections by the unit is natural. -/
lemma moduleUnitSection_map {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ Z) {U V : Z.Etale}
    (φ : V ⟶ U) (c : G.obj.obj (op U)) :
    moduleUnitSection Λ p G (G.obj.map φ.op c) =
      ((etaleModuleInverseImage.{u, 0} Λ p).obj G).obj.map ((smallEtaleBaseChange p).map φ).op
        (moduleUnitSection Λ p G c) :=
  ConcreteCategory.congr_hom (((etaleModuleInverseImageAdj.{u, 0} Λ p).unit.app G).hom.naturality
    φ.op) c

/-- Applying two restriction maps successively is the restriction along the composite. -/
private lemma map_op_map_op_apply {C : Type*} [Category C] {R : Type*} [Ring R]
    (F : Cᵒᵖ ⥤ ModuleCat.{u + 1} R) {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (x : F.obj (op X)) :
    F.map g.op (F.map f.op x) = F.map (g ≫ f).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- `sectionPairingPushforwardFun` is natural in the étale `Z`-scheme `U`. -/
lemma sectionPairingPushforwardFun_naturality {U V : Z.Etale} (φ : V ⟶ U) (a : G₁.obj.obj (op U)) :
    sectionPairingPushforwardFun p b hr s (op V) (G₁.obj.map φ.op a) =
      ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.map ((smallEtaleBaseChange p).map φ).op
        (sectionPairingPushforwardFun p b hr s (op U) a) := by
  let N := (etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃
  let φW := etaleFiberMap W φ
  have h₁ : G₁.obj.map (etaleFiberFst V W).op (G₁.obj.map φ.op a) =
      G₁.obj.map φW.op (G₁.obj.map (etaleFiberFst U W).op a) := by
    rw [map_op_map_op_apply, map_op_map_op_apply, etaleFiberMap_fst]
  have h₂ : G₂.obj.map (etaleFiberSnd V W).op s =
      G₂.obj.map φW.op (G₂.obj.map (etaleFiberSnd U W).op s) := by
    rw [map_op_map_op_apply, etaleFiberMap_snd]
  have h₃ := (b.naturality φW.op (G₁.obj.map (etaleFiberFst U W).op a)
    (G₂.obj.map (etaleFiberSnd U W).op s)).symm
  have h₄ := moduleUnitSection_map p G₃ φW (b.app (op (etaleFiberObj U W))
    (G₁.obj.map (etaleFiberFst U W).op a) (G₂.obj.map (etaleFiberSnd U W).op s))
  have h₅ : ∀ x, N.obj.map (etaleFiberLift V p hr).op
      (N.obj.map ((smallEtaleBaseChange p).map φW).op x) =
      N.obj.map ((smallEtaleBaseChange p).map φ).op (N.obj.map (etaleFiberLift U p hr).op x) := by
    intro x
    rw [map_op_map_op_apply, map_op_map_op_apply, etaleFiberLift_naturality]
  change N.obj.map (etaleFiberLift V p hr).op (moduleUnitSection Λ₃ p G₃
      (b.app (op (etaleFiberObj V W)) (G₁.obj.map (etaleFiberFst V W).op (G₁.obj.map φ.op a))
        (G₂.obj.map (etaleFiberSnd V W).op s))) =
    N.obj.map ((smallEtaleBaseChange p).map φ).op (N.obj.map (etaleFiberLift U p hr).op
      (moduleUnitSection Λ₃ p G₃ (b.app (op (etaleFiberObj U W))
        (G₁.obj.map (etaleFiberFst U W).op a) (G₂.obj.map (etaleFiberSnd U W).op s))))
  rw [h₁, h₂, h₃, h₄, h₅]

/-- **`a ↦ b(a, s)` pulled back along `(id, r)`, as a morphism `G₁ ⟶ p_*p⁻¹G₃`** of sheaves of
`ℤ`-modules on `Z_étale`. -/
def sectionPairingPushforwardMap :
    (etaleModuleRestrictScalars (Int.castRingHom Λ₁) Z).obj G₁ ⟶
      (etaleModuleDirectImage.{u, 0} ℤ p).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ₃) T).obj
          ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃)) where
  hom :=
    { app U := restrictScalarsIntOfAddHom (sectionPairingPushforwardFun p b hr s U)
      naturality _ _ f := ModuleCat.hom_ext <| LinearMap.ext fun a =>
        sectionPairingPushforwardFun_naturality p b hr s f.unop a }

/-- **The morphism `p⁻¹G₁ ⟶ p⁻¹G₃` defined by the section `s` of `G₂` over `W`** and the lift
`r : T ⟶ W` of `p`: the transpose of `Stacks.EtaleCohomology.sectionPairingPushforwardMap` for
`p⁻¹ ⊣ p_*`, on the sheaves of `ℤ`-modules obtained by restricting scalars. -/
def sectionPairingAct :
    (etaleModuleRestrictScalars (Int.castRingHom Λ₁) T).obj
        ((etaleModuleInverseImage.{u, 0} Λ₁ p).obj G₁) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ₃) T).obj
        ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃) :=
  (etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ₁) p).inv.app G₁ ≫
    ((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv _ _).symm
      (sectionPairingPushforwardMap p b hr s)

/-- Restriction of scalars carries the unit section of `p⁻¹` to the unit section. -/
lemma moduleUnitSection_restrictScalars {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ Z)
    {U : Z.Etale} (a : G.obj.obj (op U)) :
    ((etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ) p).hom.app G).hom.app
        (op ((smallEtaleBaseChange p).obj U))
        (moduleUnitSection ℤ p ((etaleModuleRestrictScalars (Int.castRingHom Λ) Z).obj G) a) =
      moduleUnitSection Λ p G a := by
  have h := congrArg (fun φ => φ.hom.app (op U))
    (coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange p) Z.smallEtaleTopology
      T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) G)
  exact (ConcreteCategory.congr_hom h a).symm

/-- **On a pulled back section, the morphism is the pairing with `s`**: `a ∈ G₁(U)` goes to
`b(a, s)` over `U ×_Z W`, pulled back along `(id, r)`. -/
lemma sectionPairingAct_moduleUnitSection {U : Z.Etale} (a : G₁.obj.obj (op U)) :
    (sectionPairingAct p b hr s).hom.app (op ((smallEtaleBaseChange p).obj U))
        (moduleUnitSection Λ₁ p G₁ a) =
      sectionPairingPushforwardFun p b hr s (op U) a := by
  rw [← moduleUnitSection_restrictScalars p G₁ a]
  change ((((etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ₁) p).hom.app G₁ ≫
      (etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ₁) p).inv.app G₁) ≫
      ((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv _ _).symm
        (sectionPairingPushforwardMap p b hr s)).hom.app _)
      (moduleUnitSection ℤ p ((etaleModuleRestrictScalars (Int.castRingHom Λ₁) Z).obj G₁) a) = _
  rw [Iso.hom_inv_id_app, Category.id_comp]
  have h := congrArg (fun φ => φ.hom.app (op U))
    (((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv_unit _ _
      (((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv _ _).symm
        (sectionPairingPushforwardMap p b hr s))).symm.trans
      (((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv _ _).apply_symm_apply _))
  exact ConcreteCategory.congr_hom h a

/-- **Pulling back a restricted section**, for any `p`: the section `a ∈ G(W)` pulled back along
`r' ≫ φ` is `φ^* a` pulled back along `r'`. -/
lemma moduleUnitSection_map_smallEtaleBaseChangeLift {Λ : Type} [Ring Λ]
    (G : EtaleModules.{u, 0} Λ Z) {V V' : Z.Etale} (φ : V' ⟶ V) (a : G.obj.obj (op V))
    {r' : T ⟶ V'.left} (hr' : r' ≫ V'.hom = p) (hr'' : (r' ≫ φ.left) ≫ V.hom = p) :
    ((etaleModuleInverseImage.{u, 0} Λ p).obj G).obj.map
        (smallEtaleBaseChangeLift p V (r' ≫ φ.left) hr'').op (moduleUnitSection Λ p G a) =
      ((etaleModuleInverseImage.{u, 0} Λ p).obj G).obj.map
        (smallEtaleBaseChangeLift p V' r' hr').op (moduleUnitSection Λ p G (G.obj.map φ.op a)) := by
  have hl : smallEtaleBaseChangeLift p V' r' hr' ≫ (smallEtaleBaseChange p).map φ =
      smallEtaleBaseChangeLift p V (r' ≫ φ.left) hr'' := by
    apply smallEtaleBaseChange_hom_ext
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ φ.left) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _).symm
  rw [moduleUnitSection_map p G φ a, ← hl, ← map_op_map_op_apply]

/-- **The morphism on a section pulled back from `U`**: for `t : U ⟶ W` and a lift `r'` of `p`
to `U` with `r = t ∘ r'`, the section `a ∈ G₁(U)` pulled back along `r'` goes to `b(a, t^* s)`
pulled back along `r'`. -/
lemma sectionPairingAct_smallEtaleBaseChangeLift {U : Z.Etale} (t : U ⟶ W) {r' : T ⟶ U.left}
    (hr' : r' ≫ U.hom = p) (hrt : r' ≫ t.left = r) (a : G₁.obj.obj (op U)) :
    (sectionPairingAct p b hr s).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        (((etaleModuleInverseImage.{u, 0} Λ₁ p).obj G₁).obj.map
          (smallEtaleBaseChangeLift p U r' hr').op (moduleUnitSection Λ₁ p G₁ a)) =
      ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.map
        (smallEtaleBaseChangeLift p U r' hr').op
        (moduleUnitSection Λ₃ p G₃ (b.app (op U) a (G₂.obj.map t.op s))) := by
  let N := (etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃
  let σ := etaleFiberSection W t
  have hnat := ConcreteCategory.congr_hom
    ((sectionPairingAct p b hr s).hom.naturality (smallEtaleBaseChangeLift p U r' hr').op)
    (moduleUnitSection Λ₁ p G₁ a)
  refine hnat.trans ?_
  change N.obj.map (smallEtaleBaseChangeLift p U r' hr').op
      ((sectionPairingAct p b hr s).hom.app (op ((smallEtaleBaseChange p).obj U))
        (moduleUnitSection Λ₁ p G₁ a)) = _
  rw [sectionPairingAct_moduleUnitSection, sectionPairingPushforwardFun_apply,
    map_op_map_op_apply, smallEtaleBaseChangeLift_comp_etaleFiberLift U p hr t hr' hrt,
    moduleUnitSection_map_smallEtaleBaseChangeLift p G₃ σ _ hr', b.naturality σ.op,
    map_op_map_op_apply, etaleFiberSection_fst, map_op_map_op_apply, etaleFiberSection_snd,
    op_id, CategoryTheory.Functor.map_id]
  rfl

omit [Ring Λ₂] in
/-- **A morphism out of `p⁻¹G₁` is determined by its values on pulled back sections.** -/
lemma sectionPairingAct_ext {f g : (etaleModuleRestrictScalars (Int.castRingHom Λ₁) T).obj
        ((etaleModuleInverseImage.{u, 0} Λ₁ p).obj G₁) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ₃) T).obj
        ((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃)}
    (h : ∀ (U : Z.Etale) (a : G₁.obj.obj (op U)),
      f.hom.app (op ((smallEtaleBaseChange p).obj U)) (moduleUnitSection Λ₁ p G₁ a) =
        g.hom.app (op ((smallEtaleBaseChange p).obj U)) (moduleUnitSection Λ₁ p G₁ a)) :
    f = g := by
  let e := (etaleModuleInverseImageRestrictScalars (Int.castRingHom Λ₁) p).app G₁
  suffices e.hom ≫ f = e.hom ≫ g from (cancel_epi _).1 this
  apply ((etaleModuleInverseImageAdj.{u, 0} ℤ p).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun a => ?_)))
  change f.hom.app (op ((smallEtaleBaseChange p).obj U.unop))
      (e.hom.hom.app _ (moduleUnitSection ℤ p _ a)) =
    g.hom.app (op ((smallEtaleBaseChange p).obj U.unop))
      (e.hom.hom.app _ (moduleUnitSection ℤ p _ a))
  exact (congrArg _ (moduleUnitSection_restrictScalars p G₁ (U := U.unop) a)).trans
    ((h U.unop a).trans (congrArg _ (moduleUnitSection_restrictScalars p G₁ (U := U.unop) a)).symm)

/-- **The morphism does not depend on the étale neighbourhood**: replacing `(W, r, s)` by
`(W', r', t^* s)` for `t : W' ⟶ W` with `r = t ∘ r'` gives the same morphism. -/
lemma sectionPairingAct_map {W' : Z.Etale} (t : W' ⟶ W) {r' : T ⟶ W'.left}
    (hr' : r' ≫ W'.hom = p) (hrt : r' ≫ t.left = r) :
    sectionPairingAct p b hr' (G₂.obj.map t.op s) = sectionPairingAct p b hr s := by
  refine sectionPairingAct_ext p fun U a => ?_
  rw [sectionPairingAct_moduleUnitSection, sectionPairingAct_moduleUnitSection,
    sectionPairingPushforwardFun_apply, sectionPairingPushforwardFun_apply]
  let ψ := etaleFiberMapRight U t
  have h₁ : G₁.obj.map (etaleFiberFst U W').op a =
      G₁.obj.map ψ.op (G₁.obj.map (etaleFiberFst U W).op a) := by
    rw [map_op_map_op_apply, etaleFiberMapRight_fst]
  have h₂ : G₂.obj.map (etaleFiberSnd U W').op (G₂.obj.map t.op s) =
      G₂.obj.map ψ.op (G₂.obj.map (etaleFiberSnd U W).op s) := by
    rw [map_op_map_op_apply, map_op_map_op_apply, etaleFiberMapRight_snd]
  rw [h₁, h₂, ← b.naturality ψ.op, moduleUnitSection_map p G₃ ψ, map_op_map_op_apply,
    etaleFiberLift_mapRight U p hr t hr' hrt]

/-- **The morphism is additive in the section.** -/
lemma sectionPairingAct_add (s' : G₂.obj.obj (op W)) :
    sectionPairingAct p b hr (s + s') =
      sectionPairingAct p b hr s + sectionPairingAct p b hr s' := by
  refine sectionPairingAct_ext p fun U a => ?_
  rw [Sheaf.Hom.add_app]
  change _ = (sectionPairingAct p b hr s).hom.app _ (moduleUnitSection Λ₁ p G₁ a) +
    (sectionPairingAct p b hr s').hom.app _ (moduleUnitSection Λ₁ p G₁ a)
  rw [sectionPairingAct_moduleUnitSection, sectionPairingAct_moduleUnitSection,
    sectionPairingAct_moduleUnitSection, sectionPairingPushforwardFun_apply,
    sectionPairingPushforwardFun_apply, sectionPairingPushforwardFun_apply, map_add, map_add]
  exact (congrArg (ConcreteCategory.hom (((etaleModuleInverseImage.{u, 0} Λ₃ p).obj G₃).obj.map
      (etaleFiberLift U p hr).op)) (map_add (ConcreteCategory.hom
        (((etaleModuleInverseImageAdj.{u, 0} Λ₃ p).unit.app G₃).hom.app
          (op (etaleFiberObj U W)))) _ _)).trans (map_add _ _ _)

/-- Inverse image carries pulled back sections to pulled back sections. -/
lemma inverseImage_map_moduleUnitSection {Λ : Type} [Ring Λ] {G G' : EtaleModules.{u, 0} Λ Z}
    (v : G ⟶ G') {U : Z.Etale} (a : G.obj.obj (op U)) :
    ((etaleModuleInverseImage.{u, 0} Λ p).map v).hom.app (op ((smallEtaleBaseChange p).obj U))
        (moduleUnitSection Λ p G a) = moduleUnitSection Λ p G' (v.hom.app (op U) a) :=
  (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op U))
    ((etaleModuleInverseImageAdj.{u, 0} Λ p).unit.naturality v)) a).symm

/-- **The morphism is natural in the paired sheaves**: if `b'(v₁ a, f^* s) = v₃ (b(a, f^* s))`
for all `f : V ⟶ W` and `a ∈ G₁(V)`, then `p⁻¹v₁` and `p⁻¹v₃` intertwine the two morphisms. -/
lemma sectionPairingAct_comm {G₁' : EtaleModules.{u, 0} Λ₁ Z} {G₃' : EtaleModules.{u, 0} Λ₃ Z}
    (b' : EtaleSectionPairing G₁' G₂ G₃') (v₁ : G₁ ⟶ G₁') (v₃ : G₃ ⟶ G₃')
    (hb : ∀ (V : Z.Etale) (f : V ⟶ W) (a : G₁.obj.obj (op V)),
      b'.app (op V) (v₁.hom.app (op V) a) (G₂.obj.map f.op s) =
        v₃.hom.app (op V) (b.app (op V) a (G₂.obj.map f.op s))) :
    (etaleModuleRestrictScalars (Int.castRingHom Λ₁) T).map
        ((etaleModuleInverseImage.{u, 0} Λ₁ p).map v₁) ≫ sectionPairingAct p b' hr s =
      sectionPairingAct p b hr s ≫ (etaleModuleRestrictScalars (Int.castRingHom Λ₃) T).map
        ((etaleModuleInverseImage.{u, 0} Λ₃ p).map v₃) := by
  refine sectionPairingAct_ext p fun U a => ?_
  change (sectionPairingAct p b' hr s).hom.app _
      (((etaleModuleInverseImage.{u, 0} Λ₁ p).map v₁).hom.app _ (moduleUnitSection Λ₁ p G₁ a)) =
    ((etaleModuleInverseImage.{u, 0} Λ₃ p).map v₃).hom.app _
      ((sectionPairingAct p b hr s).hom.app _ (moduleUnitSection Λ₁ p G₁ a))
  rw [inverseImage_map_moduleUnitSection, sectionPairingAct_moduleUnitSection,
    sectionPairingAct_moduleUnitSection, sectionPairingPushforwardFun_apply,
    sectionPairingPushforwardFun_apply]
  have hv := ConcreteCategory.congr_hom (v₁.hom.naturality (etaleFiberFst U W).op) a
  change v₁.hom.app _ (G₁.obj.map (etaleFiberFst U W).op a) =
    G₁'.obj.map (etaleFiberFst U W).op (v₁.hom.app _ a) at hv
  rw [← hv, hb, ← inverseImage_map_moduleUnitSection]
  exact (ConcreteCategory.congr_hom
    (((etaleModuleInverseImage.{u, 0} Λ₃ p).map v₃).hom.naturality
      (etaleFiberLift U p hr).op) _).symm

end Act

/-! ### Galois sections -/

section Galois

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] {Λ₁ Λ₂ Λ₃ : Type} [Ring Λ₁] [Ring Λ₂] [Ring Λ₃]
  {G₁ : EtaleModules.{u, 0} Λ₁ Y.left} {G₂ : EtaleModules.{u, 0} Λ₂ Y.left}
  {G₃ : EtaleModules.{u, 0} Λ₃ Y.left} (b : EtaleSectionPairing G₁ G₂ G₃)

/-- **The morphism `G₁|_{Y_K} ⟶ G₃|_{Y_K}` defined by a section `c` of `G₂` over the finite stage
`Y_E`**, through the projection `Y_K ⟶ Y_E`. -/
def fieldStageAct (i : FExt k K) (c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    (etaleModuleRestrictScalars (Int.castRingHom Λ₁) (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ₃) (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃) :=
  sectionPairingAct (fieldBaseChangeProj Y K) b (fieldStageCone_π_comp_hom Y K (op i)) c

omit [Ring Λ₂] in
/-- Restricting a section from a stage to itself is the identity. -/
lemma fieldStageRes_refl {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ Y.left) (i : FExt k K)
    (c : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageRes Λ Y K G (le_refl i) c = c := by
  change G.obj.map ((fieldStageSystem Y K).map (homOfLE (le_refl i)).op).op c = c
  rw [show homOfLE (le_refl i) = 𝟙 i from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **On a global section pulled back from a later stage, the morphism is the pairing there.** -/
theorem fieldStageAct_fieldStageSection {i j : FExt k K} (h : i ≤ j)
    (c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (a : G₁.obj.obj (op ((fieldStageSystem Y K).obj (op j)))) :
    (fieldStageAct Y K b i c).hom.app (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (fieldStageSection Λ₁ Y K G₁ j a) =
      fieldStageSection Λ₃ Y K G₃ j (b.app _ a (fieldStageRes Λ₂ Y K G₂ h c)) :=
  sectionPairingAct_smallEtaleBaseChangeLift _ b _ c ((fieldStageSystem Y K).map (homOfLE h).op)
    (fieldStageCone_π_comp_hom Y K (op j)) ((fieldStageCone Y K).w (homOfLE h).op) a

/-- **The morphism does not change when the section is restricted to a later stage.** -/
theorem fieldStageAct_fieldStageRes {i j : FExt k K} (h : i ≤ j)
    (c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    fieldStageAct Y K b j (fieldStageRes Λ₂ Y K G₂ h c) = fieldStageAct Y K b i c :=
  sectionPairingAct_map _ b _ c ((fieldStageSystem Y K).map (homOfLE h).op)
    (fieldStageCone_π_comp_hom Y K (op j)) ((fieldStageCone Y K).w (homOfLE h).op)

variable [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- **The morphism only depends on the pull back of the section to `Y_K`.** -/
theorem fieldStageAct_eq {i j : FExt k K} (c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i))))
    (c' : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op j))))
    (h : fieldStageSection Λ₂ Y K G₂ i c = fieldStageSection Λ₂ Y K G₂ j c') :
    fieldStageAct Y K b i c = fieldStageAct Y K b j c' := by
  obtain ⟨l, hil, hjl⟩ := exists_fext_le_le K i j
  obtain ⟨m, hlm, hm⟩ :=
    exists_fieldStageRes_eq_of_fieldStageSection_eq_of_le Λ₂ Y K G₂ hil hjl c c' h
  rw [← fieldStageAct_fieldStageRes Y K b (hil.trans hlm) c, hm, fieldStageAct_fieldStageRes]

/-- **The morphism `G₁|_{Y_K} ⟶ G₃|_{Y_K}` defined by a global section `e` of `G₂|_{Y_K}`**
through the pairing `b`: `e` is pulled back from a section over a finite stage `Y_E`
(`Stacks.EtaleCohomology.exists_fieldStageSection_eq`), which acts through
`Stacks.EtaleCohomology.fieldStageAct`; the result does not depend on the stage
(`Stacks.EtaleCohomology.galoisSectionAct_eq`). On global sections it is the Galois pairing with
`e` (`Stacks.EtaleCohomology.galoisSectionAct_ΓRes`). -/
def galoisSectionAct
    (e : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    (etaleModuleRestrictScalars (Int.castRingHom Λ₁) (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁) ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ₃) (fieldBaseChange Y K)).obj
        ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃) :=
  fieldStageAct Y K b (exists_fieldStageSection_eq Λ₂ Y K G₂ e).choose
    (exists_fieldStageSection_eq Λ₂ Y K G₂ e).choose_spec.choose

/-- **The morphism of a Galois section, through any stage representative.** -/
theorem galoisSectionAct_eq
    {e : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)}
    {i : FExt k K} {c : G₂.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (h : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) e = fieldStageSection Λ₂ Y K G₂ i c) :
    galoisSectionAct Y K b e = fieldStageAct Y K b i c :=
  fieldStageAct_eq Y K b _ _
    ((exists_fieldStageSection_eq Λ₂ Y K G₂ e).choose_spec.choose_spec.symm.trans h)

/-- **On global sections, the morphism of `e` is the Galois pairing with `e`**:
`Γ(Y_K, act(e))(z) = ⟨z, e⟩`, read on the final object of the site. -/
theorem galoisSectionAct_ΓRes
    (e : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂))
    (z : (etaleModuleGlobalSections.{u, 0} Λ₁ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁)) :
    (galoisSectionAct Y K b e).hom.app (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (((etaleModuleInverseImage.{u, 0} Λ₁ (fieldBaseChangeProj Y K)).obj G₁).ΓRes
          (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z) =
      ((etaleModuleInverseImage.{u, 0} Λ₃ (fieldBaseChangeProj Y K)).obj G₃).ΓRes
        (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K))))
        (galoisGlobalSectionsPairing Y K b z e) := by
  obtain ⟨i, -, a, c, h₁, h₂⟩ := exists_fieldStageSection_eq₂ Y K z e ⊥
  rw [galoisSectionAct_eq Y K b h₂, h₁, fieldStageAct_fieldStageSection Y K b (le_refl i),
    fieldStageRes_refl, ΓRes_galoisGlobalSectionsPairing Y K b h₁ h₂]

/-- **The morphism is additive in the Galois section.** -/
theorem galoisSectionAct_add
    (e e' : (etaleModuleGlobalSections.{u, 0} Λ₂ (fieldBaseChange Y K)).obj
      ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂)) :
    galoisSectionAct Y K b (e + e') = galoisSectionAct Y K b e + galoisSectionAct Y K b e' := by
  obtain ⟨i, -, c, c', h, h'⟩ := exists_fieldStageSection_eq₂ Y K e e' ⊥
  have hs : ((etaleModuleInverseImage.{u, 0} Λ₂ (fieldBaseChangeProj Y K)).obj G₂).ΓRes
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) (e + e') =
        fieldStageSection Λ₂ Y K G₂ i (c + c') := by
    rw [map_add, h, h', fieldStageSection_add]
  rw [galoisSectionAct_eq Y K b hs, galoisSectionAct_eq Y K b h, galoisSectionAct_eq Y K b h']
  exact sectionPairingAct_add _ b _ c c'

end Galois

end Stacks.EtaleCohomology

end
