module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionObstruction
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to lifting a map of extensions

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces, let

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0    and    0 ⟶ i_* ℒ ⟶ 𝒢' ⟶ i_* 𝒢 ⟶ 0

be extensions of `𝒪_{X'}`-modules as in Tag 08L4, and let `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ` be maps
for which the square

    ℐ ⊗_{𝒪_X} ℱ --c_{ℱ'}--> 𝒦
        |                    |
      1 ⊗ φ                  ψ
        v                    v
    ℐ ⊗_{𝒪_X} 𝒢 --c_{𝒢'}--> ℒ

commutes — the conclusion of Tag 08L5, part (1). This file produces the class

    o(φ, ψ) ∈ Ext¹_{𝒪_X}(ℱ, ℒ)

whose vanishing is necessary and sufficient for the existence of an `𝒪_{X'}`-module map
`φ' : ℱ' ⟶ 𝒢'` compatible with `φ` and `ψ`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.mapLiftingObstruction`: the class `o(φ, ψ)` together
  with its vanishing criterion.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.essImage_of_extensionAction_eq_zero`: an extension
  whose canonical map of Tag 08L4 vanishes has middle term in the essential image of `i_*`, so
  it descends to `X`.

## References

* [Stacks Project, Tag 08L6](https://stacks.math.columbia.edu/tag/08L6)
* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor

namespace CategoryTheory.Preadditive

variable {C : Type*} [Category C] [Preadditive C]

/-- A map that equalises two morphisms kills their difference. -/
theorem comp_sub_eq_zero {T A B : C} (c : T ⟶ A) (u v : A ⟶ B) (h : c ≫ u = c ≫ v) :
    c ≫ (u - v) = 0 := by
  rw [comp_sub, h, sub_self]

/-- A composite `a ≫ (b ≫ 0) ≫ c` through a zero morphism vanishes. -/
theorem comp_comp_zero_comp {A B T W V : C} (a : A ⟶ B) (b : B ⟶ T) (c : W ⟶ V) :
    a ≫ (b ≫ (0 : T ⟶ W)) ≫ c = 0 := by
  simp

/-- A sum of two composites, after a further map which transforms the two second factors in a
known way. -/
theorem add_comp_comp_eq {T A B W V : C} (u : T ⟶ A) (a : A ⟶ W) (v : T ⟶ B) (b : B ⟶ W)
    (c : W ⟶ V) {p : A ⟶ V} {q : B ⟶ V} (ha : a ≫ c = p) (hb : b ≫ c = q) :
    (u ≫ a + v ≫ b) ≫ c = u ≫ p + v ≫ q := by
  rw [add_comp, Category.assoc, Category.assoc, ha, hb]

/-- `add_comp_comp_eq` when the second summand's second factor is killed. -/
theorem add_comp_comp_eq_of_comp_eq_zero {T A B W V : C} (u : T ⟶ A) (a : A ⟶ W) (v : T ⟶ B)
    (b : B ⟶ W) (c : W ⟶ V) {p : A ⟶ V} (ha : a ≫ c = p) (hb : b ≫ c = 0) :
    (u ≫ a + v ≫ b) ≫ c = u ≫ p := by
  rw [add_comp, Category.assoc, Category.assoc, ha, hb, comp_zero, add_zero]

/-- `add_comp_comp_eq` when the first summand's second factor is killed. -/
theorem add_comp_comp_eq_of_comp_eq_zero_left {T A B W V : C} (u : T ⟶ A) (a : A ⟶ W)
    (v : T ⟶ B) (b : B ⟶ W) (c : W ⟶ V) (ha : a ≫ c = 0) :
    (u ≫ a + v ≫ b) ≫ c = v ≫ b ≫ c := by
  rw [add_comp, Category.assoc, Category.assoc, ha, comp_zero, zero_add]

/-- Recombining a difference against the term it was taken from. -/
theorem comp_comp_add_sub_comp {T A W V : C} (u : T ⟶ A) (w : A ⟶ W) (y : T ⟶ W) (c : W ⟶ V) :
    u ≫ w ≫ c + (y - u ≫ w) ≫ c = y ≫ c := by
  rw [sub_comp, Category.assoc]
  abel

end CategoryTheory.Preadditive

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Abelian C]

/-- The first component of the inclusion of the kernels into the sequence of pairs. -/
theorem pairShortComplex_f_fst (S T : ShortComplex C) (φ : S.X₃ ⟶ T.X₃) :
    (pairShortComplex S T φ).f ≫ pullback.fst (S.g ≫ φ) T.g = biprod.fst ≫ S.f :=
  pullback.lift_fst _ _ _

/-- The second component of the inclusion of the kernels into the sequence of pairs. -/
theorem pairShortComplex_f_snd (S T : ShortComplex C) (φ : S.X₃ ⟶ T.X₃) :
    (pairShortComplex S T φ).f ≫ pullback.snd (S.g ≫ φ) T.g = biprod.snd ≫ T.f :=
  pullback.lift_snd _ _ _

end CategoryTheory.Abelian

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}} (i : X ⟶ X')

/-- The tensor product of two identities of sheaves of modules on a ringed space is the
identity. -/
theorem tensorSheafMap_id_id (Y : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩)).map (((𝟙 A), (𝟙 B)) : (A, B) ⟶ (A, B))) =
      𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y)).presheaf, ((Y)).IsSheaf⟩).obj (A)).obj (B))) :=
  (tensorSheafMap_eq_tensorSheaf_map (𝟙 A) (𝟙 B)).trans
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).map_id (A, B))

/-- An extension across a first order thickening whose canonical map of Tag 08L4 vanishes has
its middle term in the essential image of `i_*`, hence descends to `X`. -/
theorem essImage_of_extensionAction_eq_zero (hi : IsFirstOrderThickening i)
    (F L : SheafOfModules.{u} (structureSheafRing X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj L) 0)
    (h : (modulePushforward i).map (firstOrderExtensionAction i F L hi E).val = 0) :
    (modulePushforward i).essImage E.Z.left := by
  refine essImage_of_idealAction_eq_zero i hi.1 E.Z.left ?_
  exact (firstOrderExtensionAction_comp i F L hi E).symm.trans
    ((congrArg (fun z => ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X')).presheaf, ((X')).IsSheaf⟩)).map
        (((𝟙 (AlgebraicGeometry.SheafOfModules.idealSheaf i)), E.g) :
          (AlgebraicGeometry.SheafOfModules.idealSheaf i, E.Z.left) ⟶
            (AlgebraicGeometry.SheafOfModules.idealSheaf i, (modulePushforward i).obj F))) ≫
          (extensionTensorComparison i F ≫ z) ≫ E.f) h).trans
      (comp_comp_zero_comp _ _ _))

/-- The obstruction `o(φ, ψ) ∈ Ext¹_{𝒪_X}(ℱ, ℒ)` to lifting a pair of maps `φ : ℱ ⟶ 𝒢` and
`ψ : 𝒦 ⟶ ℒ`, compatible with the canonical maps of two extensions across a first order
thickening, to a map of the extensions themselves: the class vanishes exactly when an
`𝒪_{X'}`-module map `φ' : ℱ' ⟶ 𝒢'` inducing `ψ` on kernels and `φ` on quotients exists. -/
@[stacks 08L6 "the obstruction class and its vanishing criterion"]
noncomputable def mapLiftingObstruction
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hi : IsFirstOrderThickening i) (F K G L : SheafOfModules.{u} (structureSheafRing X))
    (E : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0)
    (E' : CategoryTheory.Abelian.YonedaExtension
      ((modulePushforward i).obj G) ((modulePushforward i).obj L) 0)
    (φ : F ⟶ G) (ψ : K ⟶ L)
    (hcompat : (firstOrderExtensionAction i F K hi E).val ≫ ψ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), φ) :
          ((idealSheafPullback i), F) ⟶ ((idealSheafPullback i), G))) ≫
        (firstOrderExtensionAction i G L hi E').val) :
    { o : CategoryTheory.Abelian.zExt F L 1 //
      o = 0 ↔ ∃ φ' : E.Z.left ⟶ E'.Z.left,
        E.f ≫ φ' = (modulePushforward i).map ψ ≫ E'.f ∧
          φ' ≫ E'.g = E.g ≫ (modulePushforward i).map φ } :=
  Classical.indefiniteDescription _ (by
    classical
    have : (modulePushforward i).Full :=
      (closedQuotientOfIsThickening i hi.1).full_modulePushforward
    have : (modulePushforward i).Faithful :=
      (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
    have : (modulePushforward i).IsRightAdjoint := modulePushforward_isRightAdjoint i
    have : PreservesBinaryBiproduct K L (modulePushforward i) :=
      preservesBinaryBiproduct_of_preservesBinaryProduct _
    let S := ShortComplex.mk E.f E.g (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E)
    let S' := ShortComplex.mk E'.f E'.g (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E')
    have hS : S.ShortExact := CategoryTheory.Abelian.YonedaExtension.shortExact E
    have hS' : S'.ShortExact := CategoryTheory.Abelian.YonedaExtension.shortExact E'
    have : Mono E'.f := E'.mono_f
    let R := CategoryTheory.Abelian.pullbackShortComplex S'
      (E.g ≫ (modulePushforward i).map φ)
    have hR : R.ShortExact :=
      CategoryTheory.Abelian.pullbackShortComplex_shortExact hS' _
    have := hR.epi_g
    let k : (modulePushforward i).obj K ⟶
        pullback (E.g ≫ (modulePushforward i).map φ) E'.g :=
      pullback.lift E.f ((modulePushforward i).map ψ ≫ E'.f) (by
        rw [← Category.assoc, CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E, zero_comp,
          Category.assoc, CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E', comp_zero])
    have hk1 : k ≫ pullback.fst (E.g ≫ (modulePushforward i).map φ) E'.g = E.f :=
      pullback.lift_fst _ _ _
    have hk2 : k ≫ pullback.snd (E.g ≫ (modulePushforward i).map φ) E'.g =
        (modulePushforward i).map ψ ≫ E'.f := pullback.lift_snd _ _ _
    have hl1 : R.f ≫ pullback.fst (E.g ≫ (modulePushforward i).map φ) E'.g = 0 := R.zero
    have hl2 : R.f ≫ pullback.snd (E.g ≫ (modulePushforward i).map φ) E'.g = E'.f :=
      pullback.lift_snd _ _ _
    have hk : k ≫ R.g ≫ (Iso.refl E.Z.left).hom = S.f :=
      (congrArg (fun z => k ≫ z) (Category.comp_id
        (pullback.fst (E.g ≫ (modulePushforward i).map φ) E'.g))).trans hk1
    let Q := CategoryTheory.Abelian.quotientShortComplex (S := S) (T := R) k
      (Iso.refl E.Z.left) hk
    have hQ : Q.ShortExact :=
      CategoryTheory.Abelian.quotientShortComplex_shortExact hS hR k (Iso.refl _) hk
    have hp : cokernel.π k ≫ Q.g = R.g ≫ (Iso.refl E.Z.left).hom ≫ S.g :=
      CategoryTheory.Abelian.π_quotientDesc (S := S) (T := R) k (Iso.refl E.Z.left) hk
    let QE : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj L) 0 :=
      CategoryTheory.Abelian.shortExactYonedaExtension hQ
    let B := CategoryTheory.Abelian.pairShortComplex S S' ((modulePushforward i).map φ)
    have hB : B.ShortExact :=
      CategoryTheory.Abelian.pairShortComplex_shortExact hS hS' _
    let e := (modulePushforward i).mapBiprod K L
    let D := ShortComplex.mk (e.hom ≫ B.f) B.g (by
      rw [Category.assoc, B.zero, comp_zero])
    have hD : D.ShortExact :=
      ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (S₁ := B) (S₂ := D) e.symm (Iso.refl _) (Iso.refl _)
          (by simp [D]) (by simp [D])) hB
    let DE : CategoryTheory.Abelian.YonedaExtension
        ((modulePushforward i).obj F) ((modulePushforward i).obj (K ⊞ L)) 0 :=
      CategoryTheory.Abelian.shortExactYonedaExtension hD
    have hefst : ((modulePushforward i).mapBiprod K L).hom ≫ biprod.fst =
        (modulePushforward i).map biprod.fst := by
      rw [Functor.mapBiprod_hom]
      exact biprod.lift_fst _ _
    have hesnd : ((modulePushforward i).mapBiprod K L).hom ≫ biprod.snd =
        (modulePushforward i).map biprod.snd := by
      rw [Functor.mapBiprod_hom]
      exact biprod.lift_snd _ _
    have hfst : DE.f ≫ pullback.fst (E.g ≫ (modulePushforward i).map φ) E'.g =
        (modulePushforward i).map biprod.fst ≫ E.f :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => e.hom ≫ z)
            (CategoryTheory.Abelian.pairShortComplex_f_fst S S' _)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ E.f) hefst)))
    have hsnd : DE.f ≫ pullback.snd (E.g ≫ (modulePushforward i).map φ) E'.g =
        (modulePushforward i).map biprod.snd ≫ E'.f :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => e.hom ≫ z)
            (CategoryTheory.Abelian.pairShortComplex_f_snd S S' _)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ E'.f) hesnd)))
    have hmapsub : (modulePushforward i).map (biprod.snd - biprod.fst ≫ ψ) =
        (modulePushforward i).map biprod.snd -
          (modulePushforward i).map biprod.fst ≫ (modulePushforward i).map ψ := by
      rw [Functor.map_sub, Functor.map_comp]
    have hdecomp : DE.f = (modulePushforward i).map biprod.fst ≫ k +
        (modulePushforward i).map (biprod.snd - biprod.fst ≫ ψ) ≫ R.f :=
      pullback.hom_ext (f := E.g ≫ (modulePushforward i).map φ) (g := E'.g)
        (hfst.trans (add_comp_comp_eq_of_comp_eq_zero _ k _ R.f _ hk1 hl1).symm)
        (hsnd.trans ((add_comp_comp_eq _ k _ R.f _ hk2 hl2).trans
          ((congrArg (fun z => (modulePushforward i).map biprod.fst ≫
              ((modulePushforward i).map ψ ≫ E'.f) + z ≫ E'.f) hmapsub).trans
            (comp_comp_add_sub_comp _ _ _ _))).symm)
    have hQf : QE.f = R.f ≫ cokernel.π k := rfl
    have hq : DE.f ≫ cokernel.π k =
        (modulePushforward i).map (biprod.snd - biprod.fst ≫ ψ) ≫ QE.f :=
      (congrArg (fun z => z ≫ cokernel.π k) hdecomp).trans
        ((add_comp_comp_eq_of_comp_eq_zero_left _ k _ R.f (cokernel.π k)
            (cokernel.condition k)).trans
          (congrArg (fun z => (modulePushforward i).map (biprod.snd - biprod.fst ≫ ψ) ≫ z)
            hQf.symm))
    have hid : DE.g ≫ (modulePushforward i).map (𝟙 F) = DE.g :=
      (congrArg (fun z => DE.g ≫ z) ((modulePushforward i).map_id F)).trans
        (Category.comp_id DE.g)
    let TF : SheafOfModules.{u} (structureSheafRing X) :=
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
        ((idealSheafPullback i))).obj (F))
    let TG : SheafOfModules.{u} (structureSheafRing X) :=
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
        ((idealSheafPullback i))).obj (G))
    let cDE : TF ⟶ K ⊞ L :=
      (firstOrderExtensionAction i F ((K ⊞ L : SheafOfModules.{u} (structureSheafRing X))) hi
        DE).val
    let cE : TF ⟶ K := (firstOrderExtensionAction i F K hi E).val
    let cE' : TG ⟶ L := (firstOrderExtensionAction i G L hi E').val
    let cQE : TF ⟶ L := (firstOrderExtensionAction i F L hi QE).val
    let tφ : TF ⟶ TG := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), φ) :
        ((idealSheafPullback i), F) ⟶ ((idealSheafPullback i), G)))
    let tid : TF ⟶ TF := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map (((𝟙 (idealSheafPullback i)), (𝟙 F)) :
        ((idealSheafPullback i), F) ⟶ ((idealSheafPullback i), F)))
    have c₁ : cDE ≫ biprod.fst = tid ≫ cE :=
      ExtensionPair.extensionAction_naturality
        { X := X, X' := X', i := i, firstOrder := hi, F := F, K := K ⊞ L, G := F, L := K,
          firstExtension := DE, secondExtension := E, quotientMap := 𝟙 F,
          kernelMap := biprod.fst }
        { hom := pullback.fst (E.g ≫ (modulePushforward i).map φ) E'.g,
          kernel_commutes := hfst,
          quotient_commutes := hid.symm }
    have c₂ : cDE ≫ biprod.snd = tφ ≫ cE' :=
      ExtensionPair.extensionAction_naturality
        { X := X, X' := X', i := i, firstOrder := hi, F := F, K := K ⊞ L, G := G, L := L,
          firstExtension := DE, secondExtension := E', quotientMap := φ,
          kernelMap := biprod.snd }
        { hom := pullback.snd (E.g ≫ (modulePushforward i).map φ) E'.g,
          kernel_commutes := hsnd,
          quotient_commutes :=
            (pullback.condition (f := E.g ≫ (modulePushforward i).map φ) (g := E'.g)).symm.trans
              (Category.assoc _ _ _).symm }
    have c₃ : cDE ≫ (biprod.snd - biprod.fst ≫ ψ) = tid ≫ cQE :=
      ExtensionPair.extensionAction_naturality
        { X := X, X' := X', i := i, firstOrder := hi, F := F, K := K ⊞ L, G := F, L := L,
          firstExtension := DE, secondExtension := QE, quotientMap := 𝟙 F,
          kernelMap := biprod.snd - biprod.fst ≫ ψ }
        { hom := cokernel.π k,
          kernel_commutes := hq,
          quotient_commutes :=
            hp.trans ((congrArg (fun z => R.g ≫ z) (Category.id_comp S.g)).trans hid.symm) }
    have htid : tid = 𝟙 TF := tensorSheafMap_id_id X (idealSheafPullback i) F
    have e₁ : cDE ≫ biprod.fst = cE :=
      c₁.trans ((congrArg (fun z => z ≫ cE) htid).trans (Category.id_comp cE))
    have e₃ : cDE ≫ (biprod.snd - biprod.fst ≫ ψ) = cQE :=
      c₃.trans ((congrArg (fun z => z ≫ cQE) htid).trans (Category.id_comp cQE))
    have hc : cE ≫ ψ = tφ ≫ cE' := hcompat
    have hpair : cDE ≫ biprod.snd = cDE ≫ (biprod.fst ≫ ψ) :=
      (c₂.trans hc.symm).trans
        ((congrArg (fun z => z ≫ ψ) e₁).symm.trans (Category.assoc _ _ _))
    have hQzero := e₃.symm.trans (comp_sub_eq_zero cDE biprod.snd (biprod.fst ≫ ψ) hpair)
    have hmapzero := (congrArg (fun z => (modulePushforward i).map z) hQzero).trans
      ((modulePushforward i).map_zero _ _)
    have hess := essImage_of_extensionAction_eq_zero i hi F L QE hmapzero
    let o := CategoryTheory.Abelian.extClassOfEssImage (modulePushforward i) Q.f Q.g Q.zero
      hQ hess
    refine ⟨o.val, o.property.trans ?_⟩
    exact CategoryTheory.Abelian.exists_lift_iff_exists_retraction E.f E.g E'.f E'.g
      R.f R.g (pullback.snd (E.g ≫ (modulePushforward i).map φ) E'.g) k
      ((modulePushforward i).map φ) ((modulePushforward i).map ψ)
      (CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E') R.zero hS'.exact hR.exact
      hk1 hk2 hl2
      (pullback.condition (f := E.g ≫ (modulePushforward i).map φ) (g := E'.g)))

end AlgebraicGeometry.RingedSpaceThickening

end
