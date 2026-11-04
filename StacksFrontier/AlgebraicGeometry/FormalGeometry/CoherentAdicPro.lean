module

public import Mathlib.CategoryTheory.Limits.Indization.Category
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice

/-!
# Coherent adic systems as pro-objects

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`. A coherent adic system along
`I` is in particular an inverse system of quasi-coherent modules, hence determines a
pro-object of the category of quasi-coherent modules on `X`. This file proves that the
resulting functor `Coh(X, I) ⥤ Pro(QCoh(X))` is fully faithful: a coherent adic system is
determined, together with all of its morphisms, by the pro-object it presents.

Fullness is where the adic conditions enter. A morphism of pro-objects is represented at each
stage `n` by a map `F_m ⟶ G_n` out of some stage `m`; since `G_n` is annihilated by
`I ^ (n+1)` and the transitions of `F` are the quotient maps by the powers of `I`, such a map
factors through `F_n`, and the surjectivity of the transitions of `F` makes the resulting
family compatible. Faithfulness follows from the transitions of `F` being monomorphisms after
passage to the pro-category.

## Main definitions

* `AlgebraicGeometry.Scheme.QuasicoherentModules` — the category `QCoh(X)` of quasi-coherent
  modules on a scheme.
* `Stacks.Coherent.quasicoherentDiagram` and `Stacks.Coherent.quasicoherentDiagramFunctor` —
  a coherent adic system regarded as an inverse diagram of quasi-coherent modules.
* `Stacks.Coherent.coherentAdicToPro` — the canonical functor to pro-quasi-coherent modules.

## Main results

* `Stacks.Coherent.coherentAdicToPro_fullyFaithful` — the functor is fully faithful.

## Implementation notes

Pro-objects are realized as the opposite of Mathlib's ind-category of the opposite category,
`(Ind (QCoh(X))ᵒᵖ)ᵒᵖ`. Mathlib's `Ind` requires a small filtered index category in the
category's hom universe, so the index `ℕᵒᵖᵒᵖ` is transported along
`Shrink.equivalence` and `ShrinkHoms.equivalence`; the private `adic*` declarations below
carry that bookkeeping. The source's positive indexing is shifted to the zero-indexed inverse
sequences of `CoherentAdicSystems`, so the object at `n` is the source's
`F_{n+1}`. The Noetherian hypothesis of the source is not needed for full faithfulness: the
proof uses only the quotient transitions and the ideal-power annihilation.

## References

* [Stacks Project, Tag 0EIQ](https://stacks.math.columbia.edu/tag/0EIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u vC uC

namespace AlgebraicGeometry.Scheme

/-- The category `QCoh(X)` of quasi-coherent modules on a scheme, as the full subcategory of
`X.Modules` on the quasi-coherent objects. -/
public abbrev QuasicoherentModules (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

end AlgebraicGeometry.Scheme

namespace Stacks.Coherent

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

private noncomputable def indArrowPresheaf {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) (f : (Ind.lim J).obj G ⟶ (Ind.lim J).obj F) :
    colimit (G ⋙ yoneda) ⟶ colimit (F ⋙ yoneda) :=
  (Ind.limCompInclusion.app G).inv ≫ (Ind.inclusion C).map f ≫
    (Ind.limCompInclusion.app F).hom

private theorem exists_ind_stage_rep {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) (f : (Ind.lim J).obj G ⟶ (Ind.lim J).obj F) (i : J) :
    ∃ j : J, ∃ g : G.obj i ⟶ F.obj j,
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
        ((indArrowPresheaf F G f).app (op (G.obj i)))
          (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))) := by
  let E : (Cᵒᵖ ⥤ Type vC) ⥤ Type vC :=
    (evaluation Cᵒᵖ (Type vC)).obj (op (G.obj i))
  let η := indArrowPresheaf F G f
  let x : E.obj (colimit (F ⋙ yoneda)) := η.app (op (G.obj i))
    (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)))
  let e := preservesColimitIso E (F ⋙ yoneda)
  obtain ⟨j, g, hg⟩ := Concrete.colimit_exists_rep ((F ⋙ yoneda) ⋙ E) (e.hom x)
  refine ⟨j, g, ?_⟩
  have h : e.inv ((colimit.ι ((F ⋙ yoneda) ⋙ E) j) g) = x := by
    rw [hg]
    simp [x]
  have hh := ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv E (F ⋙ yoneda) j) g
  have hx := hh.symm.trans h
  simpa [E, x, η, indArrowPresheaf] using hx

private theorem colimit_yoneda_eq_of_common_stage
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J]
    (F : J ⥤ C) {i j k : J} (a : i ⟶ k) (b : j ⟶ k)
    (Y : C) (x : Y ⟶ F.obj i) (y : Y ⟶ F.obj j)
    (h : x ≫ F.map a = y ≫ F.map b) :
    ((colimit.ι (F ⋙ yoneda) i).app (op Y)) x =
      ((colimit.ι (F ⋙ yoneda) j).app (op Y)) y := by
  have ha : ((colimit.ι (F ⋙ yoneda) i).app (op Y)) x =
      ((colimit.ι (F ⋙ yoneda) k).app (op Y)) (x ≫ F.map a) := by
    have hw := congrArg (fun t => t.app (op Y) x) (colimit.w (F ⋙ yoneda) a)
    simpa [yoneda_map_app] using hw.symm
  have hb : ((colimit.ι (F ⋙ yoneda) j).app (op Y)) y =
      ((colimit.ι (F ⋙ yoneda) k).app (op Y)) (y ≫ F.map b) := by
    have hw := congrArg (fun t => t.app (op Y) y) (colimit.w (F ⋙ yoneda) b)
    simpa [yoneda_map_app] using hw.symm
  rw [ha, hb, h]

private theorem exists_common_stage_eq {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) (η : colimit (G ⋙ yoneda) ⟶ colimit (F ⋙ yoneda))
    {i i' j j' : J} (a : i ⟶ i') (g : G.obj i ⟶ F.obj j)
    (g' : G.obj i' ⟶ F.obj j')
    (hg : ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
      η.app (op (G.obj i))
        (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))))
    (hg' : ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i'))) g' =
      η.app (op (G.obj i'))
        (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))) :
    ∃ (k : J) (b : j ⟶ k) (c : j' ⟶ k),
      g ≫ F.map b = G.map a ≫ g' ≫ F.map c := by
  let E : (Cᵒᵖ ⥤ Type vC) ⥤ Type vC :=
    (evaluation Cᵒᵖ (Type vC)).obj (op (G.obj i))
  let L := (F ⋙ yoneda) ⋙ E
  have hcocone :
      ((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)) =
        ((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i))) (G.map a) :=
    colimit_yoneda_eq_of_common_stage G a (𝟙 _) _ (𝟙 _) (G.map a) (by simp)
  have hn := NatTrans.naturality_apply η (Quiver.Hom.op (G.map a))
    (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))
  have hmapι :
      ((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i)) =
        ((colimit (G ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
          (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i'))) := by
    calc
      _ = ((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i))) (G.map a) := hcocone
      _ = ((colimit (G ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
          (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i'))) := by
        have hnat := NatTrans.naturality_apply (colimit.ι (G ⋙ yoneda) i')
          (Quiver.Hom.op (G.map a)) (𝟙 (G.obj i'))
        simpa using hnat
  have hpresheaf :
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
        ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i))) (G.map a ≫ g') := by
    calc
      ((colimit.ι (F ⋙ yoneda) j).app (op (G.obj i))) g =
          η.app (op (G.obj i))
            (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 (G.obj i))) := hg
      _ = ((colimit (F ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
            (η.app (op (G.obj i'))
              (((colimit.ι (G ⋙ yoneda) i').app (op (G.obj i'))) (𝟙 (G.obj i')))) := by
        rw [hmapι]
        exact hn
      _ = ((colimit (F ⋙ yoneda)).map (Quiver.Hom.op (G.map a)))
            (((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i'))) g') := by rw [← hg']
      _ = ((colimit.ι (F ⋙ yoneda) j').app (op (G.obj i))) (G.map a ≫ g') := by
        have hnat := NatTrans.naturality_apply (colimit.ι (F ⋙ yoneda) j')
          (Quiver.Hom.op (G.map a)) g'
        simpa using hnat.symm
  let e := preservesColimitIso E (F ⋙ yoneda)
  have hcolim : (colimit.ι L j) g = (colimit.ι L j') (G.map a ≫ g') := by
    have h := congrArg e.hom hpresheaf
    simpa [L, E, e, ← ι_preservesColimitIso_hom] using h
  obtain ⟨k, b, c, hk⟩ := (Types.FilteredColimit.colimit_eq_iff L).mp hcolim
  refine ⟨k, b, c, ?_⟩
  simpa [L, E] using hk

lemma idealPowerMultiple_le_comap {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (hq : Stacks.Algebraization.idealPowerMultiple I n N ≤ Q) :
    Stacks.Algebraization.idealPowerMultiple I n M ≤
      _root_.AlgebraicGeometry.sheafSubmoduleComap f Q := by
  apply (Stacks.Algebraization.idealPowerMultiple_le_iff I n M _).2
  intro U
  let J := I.ideal U ^ n
  let fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    ModuleCat.Hom.hom (f.val.app (op U.1))
  have hqU : J • (⊤ : Submodule Γ(X, U) Γ(N, U)) ≤ Q.toSubmodule.obj (op U.1) :=
    (Stacks.Algebraization.idealPowerMultiple_le_iff I n N Q).mp hq U
  have hgen : J • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      (Q.toSubmodule.obj (op U.1)).comap fU := by
    calc
      J • (⊤ : Submodule Γ(X, U) Γ(M, U)) =
          J • ((⊤ : Submodule Γ(X, U) Γ(N, U)).comap fU) := by simp
      _ ≤ (J • (⊤ : Submodule Γ(X, U) Γ(N, U))).comap fU :=
        Submodule.smul_comap_le_comap_smul fU _ _
      _ ≤ (Q.toSubmodule.obj (op U.1)).comap fU := Submodule.comap_mono hqU
  show I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
    (Q.toSubmodule.obj (op U.1)).comap fU
  simpa [J] using hgen

/-- A coherent adic system, regarded termwise as a diagram of quasi-coherent modules. -/
public noncomputable def quasicoherentDiagram {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) :
    ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X :=
  ObjectProperty.lift _ F.obj (fun n => by
    let : (F.obj.obj n).IsCoherent := F.property.1 n.unop
    exact isQuasicoherent_of_isCoherent (F.obj.obj n))

/-- The forgetful functor on coherent adic systems, valued in inverse diagrams
of quasi-coherent modules. -/
public noncomputable def quasicoherentDiagramFunctor
    (X : Scheme.{u}) (I : X.IdealSheafData) :
    CoherentAdicSystems I ⥤
      (ℕᵒᵖ ⥤ Scheme.QuasicoherentModules X) where
  obj F := quasicoherentDiagram F
  map f :=
    { app := fun n => ObjectProperty.homMk (f.hom.app n)
      naturality := by
        intro n m a
        apply ObjectProperty.hom_ext
        exact f.hom.naturality a }
  map_id F := by
    apply NatTrans.ext
    funext n
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ObjectProperty.hom_ext
    rfl

/-- The equivalence between `ℕᵒᵖᵒᵖ` and the `u`-small category
`ShrinkHoms.{u} (Shrink.{u} ℕᵒᵖᵒᵖ)`, obtained by shrinking first the objects and then the
morphisms. -/
public noncomputable def adicIndexEquivalence :
    ℕᵒᵖᵒᵖ ≌ ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) :=
  (Shrink.equivalence.{u} (ℕᵒᵖᵒᵖ)).trans
    (ShrinkHoms.equivalence.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))

private noncomputable def adicDiagramBeforeShrink
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) :
    ℕᵒᵖᵒᵖ ⥤ (Scheme.QuasicoherentModules X)ᵒᵖ :=
  (Functor.opUnopEquiv (ℕᵒᵖ) (Scheme.QuasicoherentModules X)).functor.obj
    ((quasicoherentDiagramFunctor X I).op.obj (op F))

private noncomputable def adicDiagramMap
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (f : F ⟶ G) :
    adicDiagramBeforeShrink G ⟶ adicDiagramBeforeShrink F :=
  (Functor.opUnopEquiv (ℕᵒᵖ) (Scheme.QuasicoherentModules X)).functor.map
    ((quasicoherentDiagramFunctor X I).map f).op

private noncomputable def adicProDiagram
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) :
    ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) ⥤
      (Scheme.QuasicoherentModules X)ᵒᵖ :=
  adicIndexEquivalence.{u}.inverse ⋙ adicDiagramBeforeShrink F

private noncomputable def adicProDiagramMap
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (f : F ⟶ G) :
    adicProDiagram G ⟶ adicProDiagram F :=
  Functor.whiskerLeft adicIndexEquivalence.{u}.inverse (adicDiagramMap f)

private noncomputable def adicProStageIndex (n : ℕ) :
    ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) :=
  adicIndexEquivalence.{u}.functor.obj (op (op n))

private noncomputable def adicProStageIso
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (n : ℕ) :
    op (((quasicoherentDiagramFunctor X I).obj F).obj (op n)) ≅
      (adicProDiagram F).obj (adicProStageIndex.{u} n) := by
  exact (adicDiagramBeforeShrink F).mapIso
    (adicIndexEquivalence.{u}.unitIso.app (op (op n)))

private theorem adicProDiagramMap_stage
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (f : F ⟶ G) (n : ℕ) :
    (adicProStageIso G n).hom ≫
        (adicProDiagramMap f).app (adicProStageIndex.{u} n) =
      ((((quasicoherentDiagramFunctor X I).map f).app (op n)).op) ≫
        (adicProStageIso F n).hom := by
  let e := adicIndexEquivalence.{u}
  show (adicDiagramBeforeShrink G).map (e.unitIso.hom.app (op (op n))) ≫
      (adicDiagramMap f).app (e.inverse.obj (e.functor.obj (op (op n)))) =
    (adicDiagramMap f).app (op (op n)) ≫
      (adicDiagramBeforeShrink F).map (e.unitIso.hom.app (op (op n)))
  exact (adicDiagramMap f).naturality (e.unitIso.hom.app (op (op n)))

private noncomputable def adicIndexNumber (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) : ℕ :=
  unop (unop (adicIndexEquivalence.{u}.inverse.obj j))

private noncomputable def adicProIndexIsoAt (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :
    adicProStageIndex.{u} (adicIndexNumber.{u} j) ≅ j := by
  let e := adicIndexEquivalence.{u}
  let n := adicIndexNumber.{u} j
  have hx : e.inverse.obj j = op (op n) := by
    simp [n, adicIndexNumber, e, adicIndexEquivalence]
  change e.functor.obj (op (op n)) ≅ j
  rw [← hx]
  exact e.counitIso.app j

private noncomputable def adicProIndexArrow {n m : ℕ} (h : n ≤ m) :
    adicProStageIndex.{u} n ⟶ adicProStageIndex.{u} m :=
  adicIndexEquivalence.{u}.functor.map ((homOfLE h).op).op

private noncomputable def adicProStageIsoAt
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I)
    (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :
    op (((quasicoherentDiagramFunctor X I).obj F).obj
      (op (adicIndexNumber.{u} j))) ≅ (adicProDiagram F).obj j :=
  (adicProStageIso F (adicIndexNumber.{u} j)) ≪≫
    (adicProDiagram F).mapIso (adicProIndexIsoAt j)

private theorem coherentAdicSystem_transition_epi
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) (n : ℕ) :
    Epi (F.obj.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨e, he⟩ := F.property.2.2 n
  let q := cokernel.π
      ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
        (F.obj.obj (op (n + 1)))).ι)
  have : Epi q := by
    show Epi (Cofork.ofπ q ((cokernel.condition _).trans zero_comp.symm)).π
    exact Cofork.IsColimit.epi (s := _) (cokernelIsCokernel _)
  rw [← he]
  refine epi_comp' this ⟨fun f g h => ?_⟩
  simpa [Category.assoc] using congrArg (fun t => e.inv ≫ t) h

private theorem adicTransition_comp
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    F.obj.map (homOfLE hbc).op ≫ F.obj.map (homOfLE hab).op =
      F.obj.map (homOfLE (Nat.le_trans hab hbc)).op := by
  have h : (homOfLE hbc).op ≫ (homOfLE hab).op =
      (homOfLE (Nat.le_trans hab hbc)).op := Subsingleton.elim _ _
  simpa only [Functor.map_comp] using congrArg F.obj.map h

private theorem coherentAdicSystem_transition_epi_of_le
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) {n m : ℕ} (h : n ≤ m) :
    Epi (F.obj.map (homOfLE h).op) := by
  induction h with
  | refl => simpa using (inferInstance : Epi (𝟙 (F.obj.obj (op n))))
  | @step m h ih =>
      have hs := coherentAdicSystem_transition_epi F m
      rw [← adicTransition_comp F h (Nat.le_succ m)]
      exact epi_comp' hs ih

private theorem factor_through_adic_transition_of_annihilated
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F G : CoherentAdicSystems I) (n k : ℕ)
    (f : F.obj.obj (op (k + 1)) ⟶ G.obj.obj (op n))
    (hN : Stacks.Algebraization.idealPowerMultiple I (k + 1) (G.obj.obj (op n)) = ⊥) :
    ∃ g : F.obj.obj (op k) ⟶ G.obj.obj (op n),
      F.obj.map (homOfLE (Nat.le_succ k)).op ≫ g = f := by
  let P := Stacks.Algebraization.idealPowerMultiple I (k + 1) (F.obj.obj (op (k + 1)))
  let Q := (⊥ : (G.obj.obj (op n)).Submodule)
  let Pobj : X.Modules := P.toSheafOfModules
  let incl : Pobj ⟶ F.obj.obj (op (k + 1)) := ⟨P.ι.val⟩
  have hQ : Stacks.Algebraization.idealPowerMultiple I (k + 1) (G.obj.obj (op n)) ≤ Q := by
    rw [hN]
  have hP : P ≤ _root_.AlgebraicGeometry.sheafSubmoduleComap f Q :=
    idealPowerMultiple_le_comap I (k + 1) f Q hQ
  have hz : incl ≫ f = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.Hom.ext
    ext x
    have hx := (SheafOfModules.Submodule.le_iff.mp hP) U x.property
    change x.val ∈ (Q.toSubmodule.obj U).comap
      (ModuleCat.Hom.hom (f.val.app U)) at hx
    show (f.val.app U).hom x.val = 0
    have hxb : (ModuleCat.Hom.hom (f.val.app U)) x.val ∈
        (⊥ : (G.obj.obj (op n)).Submodule).toSubmodule.obj U := by
      simpa [Q] using (Submodule.mem_comap.mp hx)
    let Q0 : (G.obj.obj (op n)).Submodule := {
      toSubmodule := ⊥
      isSheaf := by
        intro U s hs
        have htype : Presieve.IsSheaf (Opens.grothendieckTopology X)
            ((G.obj.obj (op n)).val.presheaf ⋙ forget AddCommGrpCat) := by
          rw [← isSheaf_iff_isSheaf_of_type]
          exact GrothendieckTopology.HasSheafCompose.isSheaf _
            (G.obj.obj (op n)).isSheaf
        have hcover := htype _ hs
        have hzero : s = 0 := hcover.isSeparatedFor.ext (t₁ := s) (t₂ := 0) (by
          intro V i hi
          let : Module (X.ringCatSheaf.obj.obj (op V))
              ((G.obj.obj (op n)).val.obj (op V)) := inferInstance
          have hi' : ((G.obj.obj (op n)).val.presheaf ⋙ forget AddCommGrpCat).map i.op s ∈
              (⊥ : ((G.obj.obj (op n)).val).Submodule).obj (op V) := by
            change ((G.obj.obj (op n)).val.presheaf ⋙ forget AddCommGrpCat).map i.op s ∈
              (⊥ : ((G.obj.obj (op n)).val).Submodule).obj (op V) at hi
            exact hi
          have hz := (Submodule.mem_bot
            (R := X.ringCatSheaf.obj.obj (op V))
            (M := (G.obj.obj (op n)).val.obj (op V))).mp hi'
          change ((G.obj.obj (op n)).val.map i.op) s = 0 at hz
          show ((G.obj.obj (op n)).val.map i.op) s =
            ((G.obj.obj (op n)).val.map i.op) 0
          rw [map_zero]
          exact hz)
        show s ∈ (⊥ : ((G.obj.obj (op n)).val).Submodule).obj U
        simpa using hzero }
    have hle : (⊥ : (G.obj.obj (op n)).Submodule).toSubmodule ≤ Q0.toSubmodule :=
      (SheafOfModules.Submodule.le_iff.mp (show (⊥ : (G.obj.obj (op n)).Submodule) ≤ Q0
        from bot_le))
    have hxb0 := hle U hxb
    have hxb0' : (ModuleCat.Hom.hom (f.val.app U)) x.val ∈
        (⊥ : ((G.obj.obj (op n)).val).Submodule).obj U := by
      simpa [Q0] using hxb0
    let : Module (X.ringCatSheaf.obj.obj U)
        ((G.obj.obj (op n)).val.obj U) := inferInstance
    exact (Submodule.mem_bot (R := X.ringCatSheaf.obj.obj U)
      (M := (G.obj.obj (op n)).val.obj U)).mp (by simpa using hxb0')
  obtain ⟨e, he⟩ := F.property.2.2 k
  let q := cokernel.π incl
  let d := cokernel.desc incl f hz
  refine ⟨e.inv ≫ d, ?_⟩
  calc
    F.obj.map (homOfLE (Nat.le_succ k)).op ≫ (e.inv ≫ d) =
        (q ≫ e.hom) ≫ (e.inv ≫ d) := by
      rw [← he]
      rfl
    _ = q ≫ d := by simp [Category.assoc]
    _ = f := by simp [d, q]

private theorem idealPowerMultiple_antitone_exp {X : Scheme.{u}} (I : X.IdealSheafData)
    {m n : ℕ} (h : n ≤ m) (M : X.Modules) :
    Stacks.Algebraization.idealPowerMultiple I m M ≤
      Stacks.Algebraization.idealPowerMultiple I n M := by
  apply (Stacks.Algebraization.idealPowerMultiple_le_iff I m M _).2
  intro U
  have hpow : I.ideal U ^ m ≤ I.ideal U ^ n :=
    Ideal.pow_le_pow_right (I := I.ideal U) h
  have hsmul : I.ideal U ^ m • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) :=
    Submodule.smul_mono_left hpow
  exact hsmul.trans ((Stacks.Algebraization.idealPowerMultiple_le_iff I n M _).mp le_rfl U)

private theorem coherentAdic_annihilates_later_term
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (G : CoherentAdicSystems I) (n m : ℕ) (h : n ≤ m) :
    Stacks.Algebraization.idealPowerMultiple I (m + 1) (G.obj.obj (op n)) = ⊥ := by
  have hle := idealPowerMultiple_antitone_exp I (Nat.add_le_add_right h 1)
    (G.obj.obj (op n))
  rw [G.property.2.1 n] at hle
  exact le_bot_iff.mp hle

private theorem factor_through_adic_stage
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F G : CoherentAdicSystems I) {n m : ℕ} (h : n ≤ m)
    (f : F.obj.obj (op m) ⟶ G.obj.obj (op n)) :
    ∃ g : F.obj.obj (op n) ⟶ G.obj.obj (op n),
      F.obj.map (homOfLE h).op ≫ g = f := by
  induction h with
  | refl =>
      exact ⟨f, by simp⟩
  | @step m h ih =>
      obtain ⟨g', hg'⟩ := factor_through_adic_transition_of_annihilated
        F G n m f (coherentAdic_annihilates_later_term G n m h)
      obtain ⟨g, hg⟩ := ih g'
      refine ⟨g, ?_⟩
      rw [← adicTransition_comp F h (Nat.le_succ m), Category.assoc, hg, hg']

private def quasicoherentHomUnderlying
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} {m n : ℕ}
    (f : (quasicoherentDiagram F).obj (op m) ⟶
      (quasicoherentDiagram G).obj (op n)) :
    F.obj.obj (op m) ⟶ G.obj.obj (op n) := f.hom

private noncomputable def stageMapFromProRepresentative
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (n : ℕ)
    (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
    (g : (adicProDiagram G).obj (adicProStageIndex.{u} n) ⟶
      (adicProDiagram F).obj j) :
    F.obj.obj (op (adicIndexNumber.{u} j)) ⟶ G.obj.obj (op n) := by
  let eF := adicProStageIsoAt F j
  let h := (adicProStageIso G n).hom ≫ g ≫ eF.inv
  exact quasicoherentHomUnderlying h.unop

/-- The pro-quasi-coherent object associated with a coherent adic system. -/
public noncomputable def coherentAdicToPro
    (X : Scheme.{u}) (I : X.IdealSheafData) :
    CoherentAdicSystems I ⥤
      (Ind (Scheme.QuasicoherentModules X)ᵒᵖ)ᵒᵖ := by
  let e : ℕᵒᵖᵒᵖ ≌ ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)) :=
    (Shrink.equivalence.{u} (ℕᵒᵖᵒᵖ)).trans
      (ShrinkHoms.equivalence.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
  letI : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :=
    IsFiltered.of_equivalence e
  exact ((quasicoherentDiagramFunctor X I).op ⋙
    (Functor.opUnopEquiv _ _).functor ⋙
    (Functor.whiskeringLeft _ _ _).obj e.inverse ⋙
    Ind.lim (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).rightOp

private theorem coherentAdicToPro_map_unop
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    {F G : CoherentAdicSystems I} (f : F ⟶ G) :
    ((coherentAdicToPro X I).map f).unop =
      (Ind.lim (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).map (adicProDiagramMap f) := by
  rfl

private theorem adicProDiagram_transition_stage
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) {n m : ℕ} (h : n ≤ m) :
    (adicProStageIso (X := X) (I := I) F n).hom ≫
    (adicProDiagram (X := X) (I := I) F).map
          (adicIndexEquivalence.{u}.functor.map ((homOfLE h).op).op) =
      (((quasicoherentDiagramFunctor X I).obj F).map (homOfLE h).op).op ≫
        (adicProStageIso (X := X) (I := I) F m).hom := by
  let e := adicIndexEquivalence.{u}
  let x := op (op n)
  let y := op (op m)
  let a := ((homOfLE h).op).op
  show (adicDiagramBeforeShrink F).map (e.unitIso.hom.app x) ≫
      (adicDiagramBeforeShrink F).map (e.inverse.map (e.functor.map a)) =
    (adicDiagramBeforeShrink F).map a ≫
      (adicDiagramBeforeShrink F).map (e.unitIso.hom.app y)
  calc
    _ = (adicDiagramBeforeShrink F).map
          (e.unitIso.hom.app x ≫ e.inverse.map (e.functor.map a)) := by
      rw [← Functor.map_comp]
    _ = (adicDiagramBeforeShrink F).map (a ≫ e.unitIso.hom.app y) := by
      have hnat : e.unitIso.hom.app x ≫ e.inverse.map (e.functor.map a) =
          a ≫ e.unitIso.hom.app y := Subsingleton.elim _ _
      rw [hnat]
    _ = _ := by rw [Functor.map_comp]

private noncomputable def adicProIndexArrowFrom (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) {m : ℕ}
    (h : adicIndexNumber.{u} j ≤ m) :
    j ⟶ adicProStageIndex.{u} m :=
  (adicProIndexIsoAt j).inv ≫ adicProIndexArrow h

-- Inferring the categories through both shrinking equivalences requires additional reductions.
private theorem adicProIndexHom_ext {j k : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))}
    (a b : Quiver.Hom.{u, u} j k) : a = b := by
  exact adicIndexEquivalence.{u}.inverse.map_injective (Subsingleton.elim _ _)

private theorem adicIndexLE {j k : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))}
    (a : Quiver.Hom.{u, u} j k) :
    adicIndexNumber.{u} j ≤ adicIndexNumber.{u} k :=
  leOfHom ((adicIndexEquivalence.{u}.inverse.map a).unop.unop)

/-- Transport of `adicProDiagram_transition_stage` to the canonical arrows between stages. -/
private theorem adicProDiagram_stage_arrow
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I) {n m : ℕ} (h : n ≤ m) :
    (adicProStageIso F n).hom ≫ (adicProDiagram F).map (adicProIndexArrow.{u} h) ≫
        (adicProStageIso F m).inv =
      (((quasicoherentDiagramFunctor X I).obj F).map (homOfLE h).op).op := by
  have ht := congrArg (fun f => f ≫ (adicProStageIso F m).inv)
    (adicProDiagram_transition_stage (X := X) (I := I) F h)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at ht
  exact ht

private theorem adicProDiagram_map_to_canonical_stage
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I)
    {H : ℕ} {j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))}
    (a : j ⟶ adicProStageIndex.{u} H)
    (h : adicIndexNumber.{u} j ≤ H) :
    (adicProStageIsoAt F j).hom ≫ (adicProDiagram F).map a ≫
        (adicProStageIso F H).inv =
      (((quasicoherentDiagramFunctor X I).obj F).map (homOfLE h).op).op := by
  have hr : (adicProIndexIsoAt.{u} j).hom ≫ a = adicProIndexArrow.{u} h :=
    adicProIndexHom_ext.{u} _ _
  rw [← adicProDiagram_stage_arrow F h, ← hr, Functor.map_comp]
  simp [adicProStageIsoAt]

-- The conjugation identities involve several reindexed diagrams and equivalence isomorphisms.
private theorem adicProDiagram_map_underlying_transition
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I)
    {j k : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))}
    (a : Quiver.Hom.{u, u} j k) :
    (adicProStageIsoAt F j).hom ≫ (adicProDiagram F).map a ≫
      (adicProStageIsoAt F k).inv =
    (((quasicoherentDiagramFunctor X I).obj F).map
      (homOfLE (adicIndexLE a)).op).op := by
  have := adicProDiagram_map_to_canonical_stage F
    (a ≫ (adicProIndexIsoAt.{u} k).inv) (adicIndexLE a)
  rw [Functor.map_comp] at this
  simpa only [adicProStageIsoAt, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_inv,
    Category.assoc] using this

private structure AdicProStageRepresentative
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F G : CoherentAdicSystems I)
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) where
  /-- The index at which the morphism of pro-objects is represented. -/
  j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))
  /-- The representing morphism out of the `n`-th stage of `G`. -/
  g : (adicProDiagram G).obj (adicProStageIndex.{u} n) ⟶ (adicProDiagram F).obj j
  /-- The representing morphism does represent the component of `p` at stage `n`. -/
  property :
    ((colimit.ι (adicProDiagram F ⋙ yoneda) j).app
      (op ((adicProDiagram G).obj (adicProStageIndex.{u} n))) g) =
    ((indArrowPresheaf (adicProDiagram F) (adicProDiagram G) p.unop).app
      (op ((adicProDiagram G).obj (adicProStageIndex.{u} n)))
      (((colimit.ι (adicProDiagram G ⋙ yoneda)
        (adicProStageIndex.{u} n)).app
          (op ((adicProDiagram G).obj (adicProStageIndex.{u} n))))
        (𝟙 _)))

private noncomputable def chooseProStageRepresentative
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) : AdicProStageRepresentative F G p n := by
  apply Classical.choice
  obtain ⟨j, g, hg⟩ := exists_ind_stage_rep (adicProDiagram F) (adicProDiagram G) p.unop
    (adicProStageIndex.{u} n)
  exact ⟨⟨j, g, hg⟩⟩

private noncomputable def liftProMapComponent
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) : F.obj.obj (op n) ⟶ G.obj.obj (op n) := by
  let r := chooseProStageRepresentative F G p n
  let m := adicIndexNumber.{u} r.j
  let h := stageMapFromProRepresentative n r.j r.g
  let hk := F.obj.map (homOfLE (Nat.le_max_left m n)).op ≫ h
  exact Classical.choose (factor_through_adic_stage F G (Nat.le_max_right m n) hk)

private noncomputable def stageMapFromProRepresentativeQcoh
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I}
    (n : ℕ) (j : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
    (g : (adicProDiagram G).obj (adicProStageIndex.{u} n) ⟶
      (adicProDiagram F).obj j) :
    ((quasicoherentDiagramFunctor X I).obj F).obj
        (op (adicIndexNumber.{u} j)) ⟶
      ((quasicoherentDiagramFunctor X I).obj G).obj (op n) :=
  ObjectProperty.homMk (stageMapFromProRepresentative n j g)

private theorem stageMapFromProRepresentative_op
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) (r : AdicProStageRepresentative F G p n) :
    (stageMapFromProRepresentativeQcoh n r.j r.g).op =
      (adicProStageIso G n).hom ≫ r.g ≫
        (adicProStageIsoAt F r.j).inv := by
  rfl

-- The conjugation identities involve several reindexed diagrams and equivalence isomorphisms.
private theorem proRepresentatives_common_stage_compatible
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    {n n' : ℕ} (h : n ≤ n')
    (r : AdicProStageRepresentative F G p n)
    (r' : AdicProStageRepresentative F G p n') :
    ∃ (k : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))
      (b : r.j ⟶ k) (c : r'.j ⟶ k),
      (stageMapFromProRepresentativeQcoh n r.j r.g).op ≫
          ((((quasicoherentDiagramFunctor X I).obj F).map
            (homOfLE (adicIndexLE b)).op).op) =
        (ObjectProperty.homMk (G.obj.map (homOfLE h).op)).op ≫
          (stageMapFromProRepresentativeQcoh n' r'.j r'.g).op ≫
            ((((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (adicIndexLE c)).op).op) := by
  let a := adicProIndexArrow.{u} h
  obtain ⟨k, b, c, hcomm⟩ := exists_common_stage_eq
    (adicProDiagram F) (adicProDiagram G)
    (indArrowPresheaf (adicProDiagram F) (adicProDiagram G) p.unop)
    a r.g r'.g r.property r'.property
  let σF := adicProStageIsoAt F r.j
  let σFK := adicProStageIsoAt F k
  let σG := adicProStageIso G n
  let σG' := adicProStageIso G n'
  have hFb := adicProDiagram_map_underlying_transition F b
  have hFc := adicProDiagram_map_underlying_transition F c
  have hGmap :
      (ObjectProperty.homMk (G.obj.map (homOfLE h).op)).op =
      ((((quasicoherentDiagramFunctor X I).obj G).map (homOfLE h).op).op) := by
    congr 1
  have hGa' : σG.hom ≫ (adicProDiagram G).map a ≫ σG'.inv =
      (ObjectProperty.homMk (G.obj.map (homOfLE h).op)).op :=
    (adicProDiagram_stage_arrow G h).trans hGmap.symm
  refine ⟨k, b, c, ?_⟩
  rw [stageMapFromProRepresentative_op (X := X) (I := I) p n r,
    stageMapFromProRepresentative_op (X := X) (I := I) p n' r']
  calc
    σG.hom ≫ r.g ≫ σF.inv ≫
        (((quasicoherentDiagramFunctor X I).obj F).map
          (homOfLE (adicIndexLE b)).op).op =
      σG.hom ≫ r.g ≫ (adicProDiagram F).map b ≫ σFK.inv := by
        rw [← hFb]
        simp [σF, σFK]
    _ = σG.hom ≫ (adicProDiagram G).map a ≫ r'.g ≫
          (adicProDiagram F).map c ≫ σFK.inv := by
        simpa only [Category.assoc] using
          congrArg (fun z => σG.hom ≫ z ≫ σFK.inv) hcomm
    _ = (ObjectProperty.homMk (G.obj.map (homOfLE h).op)).op ≫
          (stageMapFromProRepresentativeQcoh n' r'.j r'.g).op ≫
          ((((quasicoherentDiagramFunctor X I).obj F).map
            (homOfLE (adicIndexLE c)).op).op) := by
        rw [← hGa', ← hFc,
          stageMapFromProRepresentative_op (X := X) (I := I) p n' r']
        simp [σFK, σG, σG', Category.assoc]

private theorem liftProMapComponent_factor
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) :
    let r := chooseProStageRepresentative F G p n
    let m := adicIndexNumber.{u} r.j
    F.obj.map (homOfLE (Nat.le_max_right m n)).op ≫ liftProMapComponent F G p n =
      F.obj.map (homOfLE (Nat.le_max_left m n)).op ≫
        stageMapFromProRepresentative n r.j r.g := by
  dsimp [liftProMapComponent]
  let r := chooseProStageRepresentative F G p n
  let m := adicIndexNumber.{u} r.j
  let h := stageMapFromProRepresentative n r.j r.g
  let hk := F.obj.map (homOfLE (Nat.le_max_left m n)).op ≫ h
  exact Classical.choose_spec
    (factor_through_adic_stage F G (Nat.le_max_right m n) hk)

/-- If `v` and `u` agree after composing with the transitions to a common stage `N`, they agree
after composing with the transitions to any later stage. -/
private theorem transition_map_comp_eq_of_factor
    {X : Scheme.{u}} {I : X.IdealSheafData} (F : CoherentAdicSystems I)
    {m n N V : ℕ} (hm : m ≤ N) (hn : n ≤ N) (hNV : N ≤ V) (hmV : m ≤ V) (hnV : n ≤ V)
    {Z : X.Modules} (u : F.obj.obj (op m) ⟶ Z) (v : F.obj.obj (op n) ⟶ Z)
    (h : F.obj.map (homOfLE hn).op ≫ v = F.obj.map (homOfLE hm).op ≫ u) :
    F.obj.map (homOfLE hnV).op ≫ v = F.obj.map (homOfLE hmV).op ≫ u := by
  rw [← adicTransition_comp F hn hNV, ← adicTransition_comp F hm hNV, Category.assoc,
    Category.assoc, h]

private theorem liftProMapComponent_natural_succ
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) :
    F.obj.map (homOfLE (Nat.le_succ n)).op ≫ liftProMapComponent F G p n =
      liftProMapComponent F G p (n + 1) ≫
        G.obj.map (homOfLE (Nat.le_succ n)).op := by
  let r₀ := chooseProStageRepresentative F G p n
  let r₁ := chooseProStageRepresentative F G p (n + 1)
  let m₀ := adicIndexNumber.{u} r₀.j
  let m₁ := adicIndexNumber.{u} r₁.j
  let H₀ := max m₀ n
  let H₁ := max m₁ (n + 1)
  let h₀ := stageMapFromProRepresentative n r₀.j r₀.g
  let h₁ := stageMapFromProRepresentative (n + 1) r₁.j r₁.g
  obtain ⟨k, b, c, hrepC⟩ := proRepresentatives_common_stage_compatible
    F G p (Nat.le_succ n) r₀ r₁
  let t := adicIndexNumber.{u} k
  let U := max (max t H₀) H₁
  have hU₀ : H₀ ≤ U :=
    Nat.le_trans (Nat.le_max_right t H₀) (Nat.le_max_left (max t H₀) H₁)
  have hU₁ : H₁ ≤ U := Nat.le_max_right (max t H₀) H₁
  have hUt : t ≤ U :=
    Nat.le_trans (Nat.le_max_left t H₀) (Nat.le_max_left (max t H₀) H₁)
  have hUn : n + 1 ≤ U :=
    Nat.le_trans (Nat.le_max_right m₁ (n + 1)) hU₁
  have hfactor₀ :
      F.obj.map (homOfLE (Nat.le_max_right m₀ n)).op ≫
          liftProMapComponent F G p n =
        F.obj.map (homOfLE (Nat.le_max_left m₀ n)).op ≫ h₀ := by
    simpa [r₀, m₀, h₀, H₀] using liftProMapComponent_factor F G p n
  have hfactor₁ :
      F.obj.map (homOfLE (Nat.le_max_right m₁ (n + 1))).op ≫
          liftProMapComponent F G p (n + 1) =
        F.obj.map (homOfLE (Nat.le_max_left m₁ (n + 1))).op ≫ h₁ := by
    simpa [r₁, m₁, h₁, H₁] using liftProMapComponent_factor F G p (n + 1)
  have hrep :
      F.obj.map (homOfLE (adicIndexLE b)).op ≫ h₀ =
        F.obj.map (homOfLE (adicIndexLE c)).op ≫ h₁ ≫
          G.obj.map (homOfLE (Nat.le_succ n)).op :=
    congrArg (fun z => z.unop.hom) hrepC
  have htU : t ≤ U := hUt
  have hm₀t : m₀ ≤ t := adicIndexLE b
  have hm₁t : m₁ ≤ t := adicIndexLE c
  have hUm₀ : m₀ ≤ U := Nat.le_trans hm₀t htU
  have hUm₁ : m₁ ≤ U := Nat.le_trans hm₁t htU
  have hU0 : n ≤ U := Nat.le_trans (Nat.le_max_right m₀ n) hU₀
  have hU1 : n + 1 ≤ U := hUn
  have hlift₀ := transition_map_comp_eq_of_factor F (Nat.le_max_left m₀ n)
    (Nat.le_max_right m₀ n) hU₀ hUm₀ hU0 h₀ (liftProMapComponent F G p n) hfactor₀
  have hlift₁ := transition_map_comp_eq_of_factor F (Nat.le_max_left m₁ (n + 1))
    (Nat.le_max_right m₁ (n + 1)) hU₁ hUm₁ hU1 h₁ (liftProMapComponent F G p (n + 1)) hfactor₁
  have hcommon : F.obj.map (homOfLE hUm₀).op ≫ h₀ =
      F.obj.map (homOfLE hUm₁).op ≫ h₁ ≫ G.obj.map (homOfLE (Nat.le_succ n)).op := by
    rw [← adicTransition_comp F hm₀t htU, ← adicTransition_comp F hm₁t htU, Category.assoc,
      Category.assoc, hrep]
  have hafter : F.obj.map (homOfLE hU1).op ≫
      (F.obj.map (homOfLE (Nat.le_succ n)).op ≫ liftProMapComponent F G p n) =
      F.obj.map (homOfLE hU1).op ≫
        (liftProMapComponent F G p (n + 1) ≫ G.obj.map (homOfLE (Nat.le_succ n)).op) := by
    rw [← Category.assoc, adicTransition_comp F (Nat.le_succ n) hU1, hlift₀, hcommon,
      ← Category.assoc, ← hlift₁, Category.assoc]
  have hepi : Epi (F.obj.map (homOfLE hU1).op) :=
    coherentAdicSystem_transition_epi_of_le F hU1
  exact hepi.left_cancellation _ _ hafter

private theorem liftProMapComponent_natural
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    {n m : ℕ} (h : n ≤ m) :
    F.obj.map (homOfLE h).op ≫ liftProMapComponent F G p n =
      liftProMapComponent F G p m ≫ G.obj.map (homOfLE h).op := by
  induction h with
  | refl => simp
  | @step m h ih =>
      calc
        F.obj.map (homOfLE (Nat.le_trans h (Nat.le_succ m))).op ≫
            liftProMapComponent F G p n =
          (F.obj.map (homOfLE (Nat.le_succ m)).op ≫
            F.obj.map (homOfLE h).op) ≫ liftProMapComponent F G p n := by
              rw [adicTransition_comp F h (Nat.le_succ m)]
        _ = F.obj.map (homOfLE (Nat.le_succ m)).op ≫
            (liftProMapComponent F G p m ≫ G.obj.map (homOfLE h).op) := by
              rw [Category.assoc, ih]
        _ = (F.obj.map (homOfLE (Nat.le_succ m)).op ≫
            liftProMapComponent F G p m) ≫ G.obj.map (homOfLE h).op := by
              rw [Category.assoc]
        _ = (liftProMapComponent F G p (m + 1) ≫
            G.obj.map (homOfLE (Nat.le_succ m)).op) ≫
              G.obj.map (homOfLE h).op := by
                rw [liftProMapComponent_natural_succ]
        _ = liftProMapComponent F G p (m + 1) ≫
            G.obj.map (homOfLE (Nat.le_trans h (Nat.le_succ m))).op := by
              rw [Category.assoc, adicTransition_comp G h (Nat.le_succ m)]

private noncomputable def liftProMapSystemHom
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G) : F ⟶ G := by
  refine ObjectProperty.homMk ?_
  refine { app := fun i => liftProMapComponent F G p i.unop, naturality := ?_ }
  intro i j f
  let h : j.unop ≤ i.unop := leOfHom f.unop
  have hf : f = (homOfLE h).op := Subsingleton.elim _ _
  rw [hf]
  exact liftProMapComponent_natural F G p h

private noncomputable def colimitMapNatTrans
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J]
    {F G : J ⥤ C} (α : G ⟶ F) :
    colimit (G ⋙ yoneda) ⟶ colimit (F ⋙ yoneda) :=
  colimMap (Functor.whiskerRight α yoneda)

private theorem colimitMapNatTrans_ι
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J]
    {F G : J ⥤ C} (α : G ⟶ F) (i : J) :
    colimit.ι (G ⋙ yoneda) i ≫ colimitMapNatTrans α =
      (Functor.whiskerRight α yoneda).app i ≫ colimit.ι (F ⋙ yoneda) i := by
  simp [colimitMapNatTrans]

private theorem indArrowPresheaf_limMap
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) (α : G ⟶ F) :
    indArrowPresheaf F G ((Ind.lim J).map α) =
      colimitMapNatTrans α := by
  have hn := (Ind.limCompInclusion (C := C) (I := J)).hom.naturality α
  have hn' :
      (Ind.inclusion C).map ((Ind.lim J).map α) ≫
          (Ind.limCompInclusion (C := C) (I := J)).hom.app F =
        (Ind.limCompInclusion (C := C) (I := J)).hom.app G ≫
          colimitMapNatTrans α := by
    simpa [Ind.lim, colimitMapNatTrans] using hn
  calc
    _ = ((Ind.limCompInclusion (C := C) (I := J)).app G).inv ≫
        (Ind.inclusion C).map ((Ind.lim J).map α) ≫
          ((Ind.limCompInclusion (C := C) (I := J)).app F).hom := rfl
    _ = colimitMapNatTrans α := by
      calc
        _ = ((Ind.limCompInclusion (C := C) (I := J)).app G).inv ≫
            ((Ind.inclusion C).map ((Ind.lim J).map α) ≫
              (Ind.limCompInclusion (C := C) (I := J)).hom.app F) := by
                rfl
        _ = ((Ind.limCompInclusion (C := C) (I := J)).app G).inv ≫
            ((Ind.limCompInclusion (C := C) (I := J)).hom.app G ≫
              colimitMapNatTrans α) :=
          congrArg (fun z => ((Ind.limCompInclusion (C := C) (I := J)).app G).inv ≫ z) hn'
        _ = _ := by simp

private theorem indArrowPresheaf_limMap_id
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) (α : G ⟶ F) (i : J) :
    (indArrowPresheaf F G ((Ind.lim J).map α)).app (op (G.obj i))
        (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 _)) =
      ((colimit.ι (F ⋙ yoneda) i).app (op (G.obj i)))
        (((Functor.whiskerRight α yoneda).app i).app
          (op (G.obj i)) (𝟙 _)) := by
  rw [indArrowPresheaf_limMap]
  simpa using congrArg (fun t => t.app (op (G.obj i)) (𝟙 (G.obj i))) (colimitMapNatTrans_ι α i)

private theorem adicProDiagramMap_stage_op
    {X : Scheme.{u}} {I : X.IdealSheafData}
    {F G : CoherentAdicSystems I} (f : F ⟶ G) (n : ℕ) :
    (adicProStageIso G n).hom ≫ (adicProDiagramMap f).app
        (adicProStageIndex.{u} n) ≫ (adicProStageIso F n).inv =
      ((((quasicoherentDiagramFunctor X I).map f).app (op n)).op) := by
  rw [← Category.assoc, adicProDiagramMap_stage f n, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem liftProRepresentative_stage_eq
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G)
    (n : ℕ) :
    let α := liftProMapSystemHom F G p
    let r := chooseProStageRepresentative F G p n
    ((colimit.ι (adicProDiagram F ⋙ yoneda) r.j).app
      (op ((adicProDiagram G).obj (adicProStageIndex.{u} n))) r.g) =
      ((colimit.ι (adicProDiagram F ⋙ yoneda)
        (adicProStageIndex.{u} n)).app
        (op ((adicProDiagram G).obj (adicProStageIndex.{u} n))))
        ((adicProDiagramMap α).app (adicProStageIndex.{u} n)) := by
  dsimp
  let r := chooseProStageRepresentative F G p n
  let α := liftProMapSystemHom F G p
  let m := adicIndexNumber.{u} r.j
  let H := max m n
  let b : r.j ⟶ adicProStageIndex.{u} H :=
    adicProIndexArrowFrom r.j (Nat.le_max_left m n)
  let c : adicProStageIndex.{u} n ⟶ adicProStageIndex.{u} H :=
    adicProIndexArrow (Nat.le_max_right m n)
  let σFH := adicProStageIso F H
  have hfactor :
      F.obj.map (homOfLE (Nat.le_max_right m n)).op ≫
          liftProMapComponent F G p n =
        F.obj.map (homOfLE (Nat.le_max_left m n)).op ≫
          stageMapFromProRepresentative n r.j r.g := by
    simpa [r, m] using liftProMapComponent_factor F G p n
  have hmaps : r.g ≫ (adicProDiagram F).map b =
      (adicProDiagramMap α).app (adicProStageIndex.{u} n) ≫
        (adicProDiagram F).map c := by
    apply (cancel_mono σFH.inv).1
    apply (cancel_epi (adicProStageIso G n).hom).1
    let σr := adicProStageIsoAt F r.j
    let τn := adicProStageIso G n
    have hleft :
        τn.hom ≫ r.g ≫ (adicProDiagram F).map b ≫
            σFH.inv =
          (stageMapFromProRepresentativeQcoh n r.j r.g).op ≫
            (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_left m n)).op).op := by
      calc
        _ = (τn.hom ≫ r.g ≫ σr.inv) ≫
              (σr.hom ≫ (adicProDiagram F).map b ≫ σFH.inv) := by
                simp [σr, Category.assoc]
        _ = _ := by
              rw [stageMapFromProRepresentative_op]
              rw [adicProDiagram_map_to_canonical_stage (F := F) b
                (Nat.le_max_left m n)]
    have hright :
        τn.hom ≫ (adicProDiagramMap α).app
            (adicProStageIndex.{u} n) ≫ (adicProDiagram F).map c ≫
            σFH.inv =
          (((quasicoherentDiagramFunctor X I).map α).app (op n)).op ≫
          (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_right m n)).op).op := by
      let σFn := adicProStageIso F n
      have hcan : σFn.hom ≫ (adicProDiagram F).map c ≫ σFH.inv =
          (((quasicoherentDiagramFunctor X I).obj F).map
            (homOfLE (Nat.le_max_right m n)).op).op := by
        exact adicProDiagram_stage_arrow F (Nat.le_max_right m n)
      calc
        _ = (τn.hom ≫ (adicProDiagramMap α).app
              (adicProStageIndex.{u} n)) ≫
              (adicProDiagram F).map c ≫ σFH.inv := by
                simp [Category.assoc]
        _ = ((((quasicoherentDiagramFunctor X I).map α).app (op n)).op ≫
              σFn.hom) ≫ (adicProDiagram F).map c ≫
              σFH.inv := by
                rw [adicProDiagramMap_stage]
        _ = (((quasicoherentDiagramFunctor X I).map α).app (op n)).op ≫
              ((((quasicoherentDiagramFunctor X I).obj F).map
                (homOfLE (Nat.le_max_right m n)).op).op) := by
                  rw [Category.assoc, hcan]
    have hfq :
        (stageMapFromProRepresentativeQcoh n r.j r.g).op ≫
            (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_left m n)).op).op =
        (((quasicoherentDiagramFunctor X I).map α).app (op n)).op ≫
            (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_right m n)).op).op := by
      have hqcoh :
          (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_left m n)).op) ≫
              stageMapFromProRepresentativeQcoh n r.j r.g =
            (((quasicoherentDiagramFunctor X I).obj F).map
              (homOfLE (Nat.le_max_right m n)).op) ≫
              ((quasicoherentDiagramFunctor X I).map α).app (op n) := by
        apply ObjectProperty.hom_ext
        exact hfactor.symm
      simpa only [op_comp] using congrArg Quiver.Hom.op hqcoh
    calc
      τn.hom ≫ r.g ≫ (adicProDiagram F).map b ≫
          σFH.inv = _ := hleft
      _ = _ := hfq
      _ = τn.hom ≫ (adicProDiagramMap α).app
            (adicProStageIndex.{u} n) ≫ (adicProDiagram F).map c ≫ σFH.inv :=
            hright.symm
  exact colimit_yoneda_eq_of_common_stage (adicProDiagram F)
    b c ((adicProDiagram G).obj (adicProStageIndex.{u} n)) r.g
    ((adicProDiagramMap α).app (adicProStageIndex.{u} n)) hmaps

private theorem indArrowPresheaf_injective
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ C) : Function.Injective (indArrowPresheaf F G) := by
  intro f g h
  apply (Ind.inclusion C).map_injective
  have h' := congrArg (fun t => (Ind.limCompInclusion.app G).hom ≫ t ≫
    (Ind.limCompInclusion.app F).inv) h
  simpa [indArrowPresheaf] using h'

private theorem liftProMapSystemHom_map
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    (F G : CoherentAdicSystems I)
    (p : (coherentAdicToPro X I).obj F ⟶ (coherentAdicToPro X I).obj G) :
    (coherentAdicToPro X I).map (liftProMapSystemHom F G p) = p := by
  apply Quiver.Hom.unop_inj
  rw [coherentAdicToPro_map_unop]
  apply indArrowPresheaf_injective (adicProDiagram F) (adicProDiagram G)
  let η := indArrowPresheaf (adicProDiagram F) (adicProDiagram G)
    ((Ind.lim _).map (adicProDiagramMap (liftProMapSystemHom F G p)))
  let θ := indArrowPresheaf (adicProDiagram F) (adicProDiagram G) p.unop
  have hs (n : ℕ) :
      colimit.ι (adicProDiagram G ⋙ yoneda) (adicProStageIndex.{u} n) ≫ η =
      colimit.ι (adicProDiagram G ⋙ yoneda) (adicProStageIndex.{u} n) ≫ θ := by
    apply yonedaEquiv.injective
    show η.app _ ((colimit.ι (adicProDiagram G ⋙ yoneda)
      (adicProStageIndex.{u} n)).app _ (𝟙 _)) =
      θ.app _ ((colimit.ι (adicProDiagram G ⋙ yoneda)
      (adicProStageIndex.{u} n)).app _ (𝟙 _))
    dsimp [η, θ]
    rw [indArrowPresheaf_limMap_id]
    simpa using (liftProRepresentative_stage_eq F G p n).symm.trans
      (chooseProStageRepresentative F G p n).property
  apply colimit.hom_ext
  intro j
  let a := adicProIndexIsoAt.{u} j
  apply (cancel_epi ((adicProDiagram G ⋙ yoneda).map a.hom)).mp
  simpa only [← Category.assoc, colimit.w] using hs (adicIndexNumber.{u} j)

private theorem indLim_map_injective_of_mono
    {C : Type uC} [Category.{vC, uC} C]
    {J : Type vC} [SmallCategory J] [IsFiltered J]
    (hJ : ∀ (i j : J) (a b : i ⟶ j), a = b)
    (F G : J ⥤ C) (hF : ∀ (i j : J) (a : i ⟶ j), Mono (F.map a))
    {α β : G ⟶ F} (h : (Ind.lim J).map α = (Ind.lim J).map β) : α = β := by
  have hη := congrArg (indArrowPresheaf F G) h
  apply NatTrans.ext
  funext i
  have hα : ((colimit.ι (F ⋙ yoneda) i).app (op (G.obj i))) (α.app i) =
      (indArrowPresheaf F G ((Ind.lim J).map α)).app (op (G.obj i))
        (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 _)) := by
    simpa using (indArrowPresheaf_limMap_id F G α i).symm
  have hβ : ((colimit.ι (F ⋙ yoneda) i).app (op (G.obj i))) (β.app i) =
      (indArrowPresheaf F G ((Ind.lim J).map α)).app (op (G.obj i))
        (((colimit.ι (G ⋙ yoneda) i).app (op (G.obj i))) (𝟙 _)) := by
    rw [hη]
    simpa using (indArrowPresheaf_limMap_id F G β i).symm
  obtain ⟨k, b, c, hk⟩ := exists_common_stage_eq F G
    (indArrowPresheaf F G ((Ind.lim J).map α)) (𝟙 i) (α.app i) (β.app i) hα hβ
  have := hF i k b
  apply (cancel_mono (F.map b)).mp
  simpa [← hJ i k b c] using hk

private theorem adicProDiagram_map_mono
    {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : CoherentAdicSystems I)
    {j k : ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))} (a : j ⟶ k) :
    Mono ((adicProDiagram F).map a) := by
  have := coherentAdicSystem_transition_epi_of_le F (adicIndexLE.{u} a)
  have : Epi (((quasicoherentDiagramFunctor X I).obj F).map
      (homOfLE (adicIndexLE.{u} a)).op) := by
    refine ⟨fun f g h => ?_⟩
    apply ObjectProperty.hom_ext
    apply (cancel_epi (F.obj.map (homOfLE (adicIndexLE.{u} a)).op)).mp
    exact congrArg (fun t => t.hom) h
  have he : (adicProDiagram F).map a =
      (adicProStageIsoAt F j).inv ≫
        ((((quasicoherentDiagramFunctor X I).obj F).map
          (homOfLE (adicIndexLE.{u} a)).op).op) ≫ (adicProStageIsoAt F k).hom := by
    rw [← adicProDiagram_map_underlying_transition F a]
    simp
  rw [he]
  infer_instance

private theorem coherentAdicToPro_map_injective
    {X : Scheme.{u}} {I : X.IdealSheafData}
    [IsFiltered.{u, u} (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))]
    {F G : CoherentAdicSystems I} {f g : F ⟶ G}
    (h : (coherentAdicToPro X I).map f = (coherentAdicToPro X I).map g) : f = g := by
  have hu : (Ind.lim (C := (Scheme.QuasicoherentModules X)ᵒᵖ)
      (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).map (adicProDiagramMap f) =
      (Ind.lim (C := (Scheme.QuasicoherentModules X)ᵒᵖ)
      (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ)))).map (adicProDiagramMap g) :=
    congrArg Quiver.Hom.unop h
  have hd := indLim_map_injective_of_mono
    (fun _ _ => adicProIndexHom_ext.{u})
    (adicProDiagram F) (adicProDiagram G) (fun _ _ => adicProDiagram_map_mono F) hu
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  have hn := congrArg (fun t => (adicProStageIso G n.unop).hom ≫
    t.app (adicProStageIndex.{u} n.unop) ≫
    (adicProStageIso F n.unop).inv) hd
  rw [adicProDiagramMap_stage_op, adicProDiagramMap_stage_op] at hn
  exact congrArg (fun t => t.unop.hom) hn

/-- A coherent adic system has exactly the morphisms of its associated
pro-quasi-coherent object. -/
@[stacks 0EIQ]
public theorem coherentAdicToPro_fullyFaithful
    (X : Scheme.{u}) (I : X.IdealSheafData) :
    Nonempty (coherentAdicToPro X I).FullyFaithful := by
  let : IsFiltered (ShrinkHoms.{u} (Shrink.{u} (ℕᵒᵖᵒᵖ))) :=
    IsFiltered.of_equivalence adicIndexEquivalence.{u}
  refine ⟨{ preimage := fun {F G} p => liftProMapSystemHom F G p
            map_preimage := fun p => liftProMapSystemHom_map _ _ p
            preimage_map := ?_ }⟩
  intro F G f
  exact coherentAdicToPro_map_injective (liftProMapSystemHom_map F G _)

end Stacks.Coherent

end
