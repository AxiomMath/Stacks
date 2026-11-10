module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitGlobal
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection

/-!
# From `colim_F Vect` to Frobenius-twisted morphisms over a scheme

This file connects the Hom-sets of the category `colim_F Vect(T)` of Stacks Tag 0EXA with the
Frobenius-twisted morphisms `HomAt` of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwist`.

* A finite locally free module has local free decompositions
  (`AlgebraicGeometry.hasLocalDecomp_of_isFiniteLocallyFree`).
* For `H : T ⟶ Y` and an object `P` of `Vect(T)` identified with `H^*M`, the iterated Frobenius
  pullbacks `F^{j,*}P` are identified with `H_j^*M` (`AlgebraicGeometry.frobIso`), and
  morphisms `F^{j,*}P ⟶ F^{j,*}Q` with morphisms `H_j^*M ⟶ H_j^*N`
  (`AlgebraicGeometry.homTransfer`), compatibly with applying `F^*`, which becomes the
  Frobenius twist (`AlgebraicGeometry.homTransfer_map`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Free modules on a finite type -/

/-- **A decomposition from an isomorphism with a finite direct sum of copies of the structure
sheaf**, given by summand inclusions and projections. -/
def FreeDecomp.ofSummands {Y T : Scheme.{u}} {K : T ⟶ Y} {A : Y.Modules} {F : T.Modules}
    {I : Type u} [Fintype I] (β : (Scheme.Modules.pullback K).obj A ≅ F)
    (ι' : I → (Scheme.unitModule T ⟶ F)) (π' : I → (F ⟶ Scheme.unitModule T))
    (h : ∑ i, π' i ≫ ι' i = 𝟙 F) : FreeDecomp K A where
  n := Fintype.card I
  ι j := (Scheme.Modules.pullbackUnitIso K).hom ≫ ι' ((Fintype.equivFin I).symm j) ≫ β.inv
  π j := β.hom ≫ π' ((Fintype.equivFin I).symm j) ≫ (Scheme.Modules.pullbackUnitIso K).inv
  total := by
    have h' : ∑ j, π' ((Fintype.equivFin I).symm j) ≫ ι' ((Fintype.equivFin I).symm j) = 𝟙 F :=
      (Equiv.sum_comp (Fintype.equivFin I).symm (fun i ↦ π' i ≫ ι' i)).trans h
    calc ∑ j, (β.hom ≫ π' ((Fintype.equivFin I).symm j) ≫
          (Scheme.Modules.pullbackUnitIso K).inv) ≫ (Scheme.Modules.pullbackUnitIso K).hom ≫
            ι' ((Fintype.equivFin I).symm j) ≫ β.inv
        = β.hom ≫ (∑ j, π' ((Fintype.equivFin I).symm j) ≫
            ι' ((Fintype.equivFin I).symm j)) ≫ β.inv := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
            Iso.inv_hom_id_assoc]
      _ = 𝟙 _ := by rw [h', Category.id_comp, Iso.hom_inv_id]

/-- **A finite locally free module has local free decompositions.** -/
theorem hasLocalDecomp_of_isFiniteLocallyFree {Y : Scheme.{u}} (M : Y.Modules)
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) : HasLocalDecomp (𝟙 Y) M := by
  intro x
  obtain ⟨U, hxU, I, hI, ⟨ε⟩⟩ := (Scheme.Modules.isFiniteLocallyFree_iff M).mpr h x
  have := Fintype.ofFinite I
  obtain ⟨W, ⟨hW⟩, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    Y.isBasis_affineOpens hxU
  let W' : Y.Opens := W
  let β := (Scheme.Modules.pullbackCongr (Category.comp_id U.ι)).app M ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ ε
  let D : FreeDecomp (U.ι ≫ 𝟙 Y) M := FreeDecomp.ofSummands β
    (fun i ↦ SheafOfModules.ιFree i) (fun i ↦ SheafOfModules.freeProjection i)
    SheafOfModules.sum_freeProjection_comp_ιFree
  exact ⟨W', ⟨hW⟩, hxW, ⟨D.restrictLE hle⟩⟩

/-! ### Iterated Frobenius pullbacks as single pullbacks -/

variable {Y : Scheme.{u}} {p : ℕ} [Fact p.Prime] {hY : IsInCharacteristic Y p}

variable (p hY) in
/-- **`F^{j,*}P ≅ H_j^*M`** for an object `P` of `Vect(T)` with `P ≅ H^*M`. -/
def frobIso {T : Scheme.{u}} (hT : IsInCharacteristic T p) (H : T ⟶ Y) {P : T.Vect}
    {M : Y.Modules} (e : P.obj ≅ (Scheme.Modules.pullback H).obj M) :
    ∀ j, (((frobeniusPullback T p hT).endoIter j).obj P).obj ≅
      (Scheme.Modules.pullback (frobPow p hY H j)).obj M
  | 0 => e
  | j + 1 => (Scheme.Modules.pullback (frobOf p hY (frobPow p hY H j))).mapIso (frobIso hT H e j) ≪≫
      (Scheme.Modules.pullbackComp (frobOf p hY (frobPow p hY H j)) (frobPow p hY H j)).app M

variable (p hY) in
/-- **Morphisms `F^{j,*}P ⟶ F^{j,*}Q` as morphisms `H_j^*M ⟶ H_j^*N`.** -/
def homTransfer {T : Scheme.{u}} (hT : IsInCharacteristic T p) (H : T ⟶ Y) {P Q : T.Vect}
    {M N : Y.Modules} (eP : P.obj ≅ (Scheme.Modules.pullback H).obj M)
    (eQ : Q.obj ≅ (Scheme.Modules.pullback H).obj N) (j : ℕ)
    (φ : ((frobeniusPullback T p hT).endoIter j).obj P ⟶
      ((frobeniusPullback T p hT).endoIter j).obj Q) :
    HomAt (frobPow p hY H j) M N :=
  (frobIso p hY hT H eP j).inv ≫ φ.hom ≫ (frobIso p hY hT H eQ j).hom

section Transfer

variable {T : Scheme.{u}} (hT : IsInCharacteristic T p) (H : T ⟶ Y) {P Q : T.Vect}
  {M N : Y.Modules} (eP : P.obj ≅ (Scheme.Modules.pullback H).obj M)
  (eQ : Q.obj ≅ (Scheme.Modules.pullback H).obj N)

/-- `homTransfer` is injective: conjugating by the isomorphisms `frobIso` loses nothing. -/
lemma homTransfer_injective (j : ℕ) :
    Function.Injective (homTransfer p hY hT H eP eQ j) := by
  intro φ ψ h
  exact ObjectProperty.hom_ext _
    (((frobIso p hY hT H eP j).homCongr (frobIso p hY hT H eQ j)).injective h)

/-- `homTransfer` is surjective: every morphism `H_j^*M ⟶ H_j^*N` is conjugate to a morphism
`F^{j,*}P ⟶ F^{j,*}Q`. -/
lemma homTransfer_surjective (j : ℕ) :
    Function.Surjective (homTransfer p hY hT H eP eQ j) := by
  intro χ
  obtain ⟨f, hf⟩ := ((frobIso p hY hT H eP j).homCongr (frobIso p hY hT H eQ j)).surjective χ
  exact ⟨ObjectProperty.homMk f, hf⟩

/-- **Applying `F^*` is the Frobenius twist.** -/
lemma homTransfer_map (j : ℕ)
    (φ : ((frobeniusPullback T p hT).endoIter j).obj P ⟶
      ((frobeniusPullback T p hT).endoIter j).obj Q) :
    homTransfer p hY hT H eP eQ (j + 1) ((frobeniusPullback T p hT).map φ) =
      twist p hY (homTransfer p hY hT H eP eQ j φ) := by
  change (Scheme.Modules.pullbackComp _ _).inv.app M ≫
      (Scheme.Modules.pullback (frobOf p hY (frobPow p hY H j))).map
        (frobIso p hY hT H eP j).inv ≫
      (Scheme.Modules.pullback (frobOf p hY (frobPow p hY H j))).map φ.hom ≫
      (Scheme.Modules.pullback (frobOf p hY (frobPow p hY H j))).map
        (frobIso p hY hT H eQ j).hom ≫ (Scheme.Modules.pullbackComp _ _).hom.app N = _
  simp only [twist, homTransfer, Functor.map_comp, Category.assoc]

/-- **Raising is the iterated twist**, up to the transport along `frobPow_add`. -/
lemma homTransfer_endoRaise (j : ℕ)
    (φ : ((frobeniusPullback T p hT).endoIter j).obj P ⟶
      ((frobeniusPullback T p hT).endoIter j).obj Q) :
    ∀ m, homTransfer p hY hT H eP eQ (j + m) (endoRaise φ m) =
      homRes (𝟙 T) (by rw [Category.id_comp, frobPow_add])
        (twistIter p hY m (homTransfer p hY hT H eP eQ j φ))
  | 0 => (homRes_one _ _).symm
  | m + 1 => by
    have ih := homTransfer_endoRaise j φ m
    refine (homTransfer_map hT H eP eQ (j + m) (endoRaise φ m)).trans ?_
    refine (congrArg (twist p hY) ih).trans ?_
    exact (homRes_twist (𝟙 T) _ _).symm

/-- Transport of the exponent is transport along the identity. -/
lemma homTransfer_endoHomCast {j j' : ℕ} (h : j = j') (h' : j = j')
    (φ : ((frobeniusPullback T p hT).endoIter j).obj P ⟶
      ((frobeniusPullback T p hT).endoIter j).obj Q) :
    homTransfer p hY hT H eP eQ j' (endoHomCast h h' φ) =
      homRes (𝟙 T) (by subst h; rw [Category.id_comp]) (homTransfer p hY hT H eP eQ j φ) := by
  subst h
  exact (homRes_one _ _).symm

end Transfer

end AlgebraicGeometry

end
