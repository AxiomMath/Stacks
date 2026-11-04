module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.EffaceableRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.DegreeZero
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer

/-!
# Restriction of étale cohomology in degree zero

For a morphism of schemes `i : Z ⟶ X` and an abelian sheaf `F` on the small étale site of `X`,
restriction `H⁰(X, F) ⟶ H⁰(Z, i⁻¹F)` is, under the identification of `H⁰` with global sections,
the unit `F ⟶ i_* i⁻¹ F` of the inverse-image/direct-image adjunction evaluated at the final
object. This file proves that, and deduces that restriction in degree zero is bijective whenever
the comparison of global sections of sheaves of *sets* along `i` is an isomorphism; the passage
from sets to abelian groups is the compatibility of inverse image with the forgetful functor
(`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`).

With [Stacks, Tag 09ZH] this gives the degree-zero case of [Stacks, Tag 09ZI].

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_isIso_comparison` —
  restriction is bijective in degree zero when the global-sections comparison for sheaves of sets
  is an isomorphism.

The case of `Spec (A ⧸ I) ⟶ Spec A` for a henselian pair `(A, I)` is the base's
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair`
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.DegreeZero`).

## References

* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-- The adjoint transpose of `c⁻¹ ≫ L.map a`, where `c` is the uniqueness isomorphism of two left
adjoints of the composite `sections ∘ pushforward`, is the transpose of `a` followed by the
image of the unit of `L ⊣ pushforward`. -/
theorem homEquiv_leftAdjointUniq_inv_comp_map
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {constantX : E ⥤ C} {sectionsX : C ⥤ E}
    {pullback : C ⥤ D} {pushforward : D ⥤ C}
    {constantY : E ⥤ D}
    (adjX : constantX ⊣ sectionsX) (adjPull : pullback ⊣ pushforward)
    (adjY : constantY ⊣ pushforward ⋙ sectionsX)
    (source : E) (target : C) (arrow : constantX.obj source ⟶ target) :
    adjY.homEquiv source (pullback.obj target)
      (((adjX.comp adjPull).leftAdjointUniq adjY).inv.app source ≫
        pullback.map arrow) =
      adjX.homEquiv source target arrow ≫ sectionsX.map (adjPull.unit.app target) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.leftAdjointUniq_inv_app, Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc,
    ← Functor.map_comp, ← adjPull.unit_naturality]

/-- Postcomposition with a bijective morphism of abelian groups is bijective on morphisms out of
`ℤ`. -/
theorem bijective_postcomp_uliftInt {A B : AddCommGrpCat.{u}} (f : A ⟶ B)
    (h : Function.Bijective f) :
    Function.Bijective (fun b : AddCommGrpCat.of (ULift ℤ) ⟶ A => b ≫ f) := by
  let E := AddCommGrpCat.uliftZMultiplesAddEquiv A
  let E' := AddCommGrpCat.uliftZMultiplesAddEquiv B
  have key : ∀ b, E' (b ≫ f) = f (E b) := fun b => rfl
  refine ⟨fun b b' hbb => E.injective (h.1 ?_), fun c => ?_⟩
  · rw [← key, ← key]
    exact congrArg E' hbb
  · obtain ⟨a, ha⟩ := h.2 (E' c)
    refine ⟨E.symm a, E'.injective ?_⟩
    rw [key, AddEquiv.apply_symm_apply]
    exact ha

section DegreeZero

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- The final object `X ⟶ X` of the small étale site of `X`. -/
abbrev etaleIdObj (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- The object `etaleIdObj X` is terminal in the small étale site of `X`. -/
private def isTerminalEtaleIdObj (X : Scheme.{u}) : IsTerminal (etaleIdObj X) :=
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- **Restriction in degree zero is bijective as soon as the unit of inverse image is bijective at
the final object.** -/
theorem bijective_etaleCohomologyRestrictionMap_zero_of_bijective_sheafAdjunctionUnit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange i)
        AddCommGrpCat.{u + 1} X.smallEtaleTopology Z.smallEtaleTopology).unit.app F).hom.app
          (op (etaleIdObj X)))) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0) := by
  let hT := isTerminalEtaleIdObj X
  let hGT := hT.isTerminalObj (smallEtaleBaseChange i)
  let adjX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  let adjPull := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology Z.smallEtaleTopology
  let adjY := constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1} hGT
  let Φ := etaleAbelianInverseImage.{u, 0} i
  let Zx := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let c := (etaleAbelianInverseImageConstantIso.{u, 0} i).app (AddCommGrpCat.of (ULift ℤ))
  -- the degree-zero map on morphisms out of the constant sheaf
  let m : (Zx ⟶ F) → ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ Φ.obj F) := fun a => c.inv ≫ Φ.map a
  have hm : ∀ a, etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0 (Ext.mk₀ a) =
      Ext.mk₀ (m a) := by
    intro a
    rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  -- `m` is postcomposition with the unit, read through the two adjunctions
  have hmeq : ∀ a, adjY.homEquiv _ _ (m a) = adjX.homEquiv _ _ a ≫
      (adjPull.unit.app F).hom.app (op (etaleIdObj X)) :=
    fun a => homEquiv_leftAdjointUniq_inv_comp_map adjX adjPull adjY _ F a
  have hmbij : Function.Bijective m := by
    have : (adjY.homEquiv _ _) ∘ m = (fun b => b ≫ (adjPull.unit.app F).hom.app
        (op (etaleIdObj X))) ∘ adjX.homEquiv _ _ := funext hmeq
    have hpost : Function.Bijective (fun b : AddCommGrpCat.of (ULift ℤ) ⟶ F.obj.obj
        (op (etaleIdObj X)) => b ≫ (adjPull.unit.app F).hom.app (op (etaleIdObj X))) := by
      exact bijective_postcomp_uliftInt _ h
    refine (Function.Bijective.of_comp_iff' (adjY.homEquiv _ _).bijective m).mp ?_
    rw [this]
    exact hpost.comp (adjX.homEquiv _ _).bijective
  have hcomp : etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0 ∘ Ext.mk₀ =
      Ext.mk₀ ∘ m := funext hm
  refine (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective Zx F)).mp ?_
  rw [hcomp]
  exact (Ext.mk₀_bijective _ _).comp hmbij

/-- Cancelling the image of an identity and an identity at the end of a composite. -/
theorem cancel_map_id_comp_id {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Fn : 𝒞 ⥤ 𝒟)
    {W : 𝒞} {Y₀ Y : 𝒟} (m : Y₀ ⟶ Y) (n : Y ⟶ Fn.obj W) :
    (m ≫ n) ≫ Fn.map (𝟙 W) ≫ 𝟙 (Fn.obj W) = m ≫ n := by
  rw [Fn.map_id, Category.id_comp, Category.comp_id]

/-- The unit of the inverse-image/direct-image adjunction of
`CategoryTheory.Functor.sheafPullbackConstruction`, on underlying presheaves: the unit of the
left Kan extension followed by the sheafification unit, restricted along the functor of sites. -/
theorem sheafPullbackConstruction_unit_hom {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
    {A : Type*} [Category* A] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]
    (c : Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c).hom =
      uf.op.leftKanExtensionUnit c.obj ≫
        Functor.whiskerLeft uf.op (toSheafify K (uf.op.leftKanExtension c.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
      (L := Functor.sheafPullbackConstruction.sheafPullback uf A J K)
      (R := uf.sheafPushforwardContinuous A J K)
      ((uf.op.lanAdjunction A).comp (sheafificationAdjunction K A))
      (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id (Sheaf K A))
      (Iso.refl _) (Iso.refl _) c
  refine h.trans ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, ObjectProperty.ι_obj, Iso.refl_hom, NatTrans.id_app]
  exact cancel_map_id_comp_id _ _ _

/-- **The unit of inverse image of sheaves of sets is bijective on global sections when the
global-sections comparison is an isomorphism.** -/
theorem isIso_unit_app_terminal_of_isIso_comparison
    (hiso : IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, 0} i).val)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange i)
        (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology).unit.app G).hom.app
          (op (terminal X.Etale))) := by
  let hb := isTerminalSmallEtaleBaseChangeObj i terminalIsTerminal
  let g : terminal Z.Etale ⟶ (smallEtaleBaseChange i).obj (terminal X.Etale) :=
    hb.from _
  have hg : IsIso g := ⟨⟨terminal.from _, terminalIsTerminal.hom_ext _ _, hb.hom_ext _ _⟩⟩
  have hmap : IsIso (smallEtaleGlobalSectionsMapAt.{u, 0} i g G) := by
    rw [← (globalSectionsSmallEtaleInverseImageComparison.{u, 0} i).2 G g]
    infer_instance
  let L := (smallEtaleBaseChange i).op.leftKanExtension G.obj
  have hnat := (toSheafify Z.smallEtaleTopology L).naturality g.op
  let T0 := op (terminal X.Etale)
  let lu := ((smallEtaleBaseChange i).op.lanUnit.app G.obj).app T0
  let ts := toSheafify Z.smallEtaleTopology L
  have hunit : ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) (Type (u + 1)) X.smallEtaleTopology
        Z.smallEtaleTopology).unit.app G).hom.app T0 =
      lu ≫ ts.app (op ((smallEtaleBaseChange i).obj (terminal X.Etale))) := by
    rw [sheafPullbackConstruction_unit_hom]
    rfl
  have hform : smallEtaleGlobalSectionsMapAt.{u, 0} i g G =
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).hom.app G ≫
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange i)
        (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology).unit.app G).hom.app T0 ≫
      (sheafify Z.smallEtaleTopology L).map g.op ≫
      (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, 0} i).obj G) := by
    rw [hunit]
    change (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).hom.app G ≫ lu ≫ L.map g.op ≫ ts.app (op (terminal Z.Etale)) ≫
      (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, 0} i).obj G) = _
    have hnat' : L.map g.op ≫ ts.app (op (terminal Z.Etale)) =
        ts.app (op ((smallEtaleBaseChange i).obj (terminal X.Etale))) ≫
          (sheafify Z.smallEtaleTopology L).map g.op := hnat
    have h' := congrArg (fun t => (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).hom.app G ≫ lu ≫ t ≫ (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology
          (Type (u + 1)) terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, 0} i).obj G))
      hnat'
    exact h'
  rw [hform] at hmap
  have := hmap
  have : IsIso ((sheafify Z.smallEtaleTopology L).map g.op) := inferInstance
  have := IsIso.of_isIso_comp_left ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    (Type (u + 1)) terminalIsTerminal).hom.app G)
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) (Type (u + 1)) X.smallEtaleTopology
        Z.smallEtaleTopology).unit.app G).hom.app T0 ≫
      (sheafify Z.smallEtaleTopology L).map g.op ≫
      (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, 0} i).obj G))
  have hrest : IsIso ((sheafify Z.smallEtaleTopology L).map g.op ≫
      (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (Type (u + 1))
        terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, 0} i).obj G)) :=
    IsIso.comp_isIso' inferInstance (Iso.isIso_inv ((Sheaf.ΓNatIsoSheafSections
      Z.smallEtaleTopology (Type (u + 1)) terminalIsTerminal).app
        ((smallEtaleInverseImage.{u, 0} i).obj G)))
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hrest (by assumption)

/-- **Inverse image commutes with forgetting the group structure, on units.** The unit of inverse
image of abelian sheaves is bijective at an object as soon as the unit of inverse image of the
underlying sheaf of sets is: the two differ by the canonical comparison
`Stacks.EtaleCohomology.coefficientPullbackComparison`, which is an isomorphism. -/
theorem bijective_unit_app_of_isIso_forget (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : X.Etale)
    (h : IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op V))) :
    Function.Bijective (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
        Z.smallEtaleTopology).unit.app F).hom.app (op V)) := by
  have hu := congrArg (fun φ => φ.hom.app (op V))
    (coefficientPullbackComparison_unit (smallEtaleBaseChange i) X.smallEtaleTopology
      Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F)
  have hc : IsIso (coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
      Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F) := by
    rw [← coefficientPullbackTwoSquare_app]
    infer_instance
  have hc' : IsIso ((coefficientPullbackComparison (smallEtaleBaseChange i)
      X.smallEtaleTopology Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F).hom.app
        (op ((smallEtaleBaseChange i).obj V))) := by
    have : IsIso (coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
      Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F).hom :=
      Functor.map_isIso (sheafToPresheaf Z.smallEtaleTopology (Type (u + 1)))
        (coefficientPullbackComparison (smallEtaleBaseChange i) X.smallEtaleTopology
          Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F)
    infer_instance
  have hcomp : IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op V) ≫
      (coefficientPullbackComparison (smallEtaleBaseChange i)
      X.smallEtaleTopology Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F).hom.app
        (op ((smallEtaleBaseChange i).obj V))) := IsIso.comp_isIso' h hc'
  have heq : ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology).unit.app
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F)).hom.app
          (op V) ≫
      (coefficientPullbackComparison (smallEtaleBaseChange i)
      X.smallEtaleTopology Z.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) F).hom.app
        (op ((smallEtaleBaseChange i).obj V)) =
      (forget AddCommGrpCat.{u + 1}).map
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (smallEtaleBaseChange i) AddCommGrpCat.{u + 1} X.smallEtaleTopology
            Z.smallEtaleTopology).unit.app F).hom.app (op V)) :=
    hu.trans rfl
  rw [heq] at hcomp
  exact (isIso_iff_bijective _).mp hcomp

/-- **Restriction is bijective in degree zero when the global-sections comparison for sheaves of
sets is an isomorphism.** -/
theorem bijective_etaleCohomologyRestrictionMap_zero_of_isIso_comparison
    (hiso : IsIso (globalSectionsSmallEtaleInverseImageComparison.{u, 0} i).val)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F 0) := by
  refine bijective_etaleCohomologyRestrictionMap_zero_of_bijective_sheafAdjunctionUnit i F ?_
  refine bijective_unit_app_of_isIso_forget i F _ ?_
  let hT := isTerminalEtaleIdObj X
  let e : op (terminal X.Etale) ≅ op (etaleIdObj X) :=
    (hT.uniqueUpToIso terminalIsTerminal).op
  exact (NatTrans.isIso_app_iff_of_iso _ e).mp
    (isIso_unit_app_terminal_of_isIso_comparison i hiso _)

end DegreeZero

/-- **Gabber's theorem from effaceability.** For a henselian pair `(A, I)`, if positive-degree
classes of torsion sheaves over `Spec A` and over `Spec (A ⧸ I)` can be effaced by monomorphisms
into torsion sheaves — the two applications of [Stacks, Tag 09ZE] in the proof of
[Stacks, Tag 09ZI] — then restriction `H^q(Spec A, F) ⟶ H^q(Spec (A ⧸ I), F|)` is bijective for
every torsion sheaf `F` and every `q`. The degree-zero case is
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair`.

No `@[stacks]` attribute: the effaceability inputs are hypotheses here. -/
theorem bijective_etaleCohomologyRestrictionMap_of_henselianPair_of_effaceable
    (A : Type u) [CommRing A] (I : Ideal A) (h : HenselianPair A I)
    (heffX : ∀ F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F → ∀ (q : ℕ), 0 < q →
      ∀ ξ : Sheaf.H.{u + 1} F q,
      ∃ (F' : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ F'),
        Mono φ ∧ Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F' ∧
          ξ.comp (Ext.mk₀ φ) (add_zero q) = 0)
    (heffY : ∀ F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F → ∀ (q : ℕ), 0 < q →
      ∀ ξ : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj F) q,
      ∃ (F' : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ F'),
        Mono φ ∧ Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F' ∧
          ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0}
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map φ)) (add_zero q) = 0)
    (q : ℕ) (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) :=
  bijective_etaleCohomologyRestrictionMap_of_effaceable _
    (Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology)
    (fun φ hF' => by
      have : Epi (cokernel.π φ) := coequalizer.π_epi
      exact (Stacks.Torsion.torsionSheafProperty.{u + 1, u, u + 1}
        (Spec (.of A)).smallEtaleTopology).prop_of_epi (cokernel.π φ) hF')
    (fun F _ => bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair A I h F)
    heffX heffY q F hF

end Stacks.EtaleCohomology
