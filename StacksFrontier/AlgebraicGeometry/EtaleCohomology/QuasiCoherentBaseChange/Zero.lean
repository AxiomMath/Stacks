module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentBaseChange.Span
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AdditiveSheafAssociatedStructure
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The base change map in degree zero

In degree zero the base change map `H⁰(X_étale, ℱᵉ) ⟶ H⁰(Y_étale, (g^* ℱ)ᵉ)` is, under the
identification of `H⁰` with sections over the final object, the pullback of sections
`Γ(X, ℱ) ⟶ Γ(X ×_X Y, …)`. For the base change `Y = X ×_{Spec k} Spec k'` of a quasi-compact
quasi-separated `X` along a field extension, the sections upstairs are spanned over `k'` by the
pullbacks of sections downstairs (flat base change in degree zero), so the base change map spans
in degree zero.

## Main results

* `AlgebraicGeometry.QcohEtale.homEquiv_restriction_zero`: the degree-zero formula.
* `AlgebraicGeometry.QcohEtale.spans_zero`: the base change map spans in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry.QcohEtale

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

section Formula

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The final object `X ⟶ X` of the small étale site of `X`, as used by
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. -/
abbrev finalObj (X : Scheme.{u}) : X.Etale :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- It is final. -/
abbrev finalObjIsTerminal (X : Scheme.{u}) : IsTerminal (finalObj X) :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- Its base change is final. -/
abbrev baseChangeFinalIsTerminal : IsTerminal ((smallEtaleBaseChange g).obj (finalObj X)) :=
  (finalObjIsTerminal X).isTerminalObj (smallEtaleBaseChange g)

/-- **The base change map in degree zero, on morphisms out of the constant sheaf.** -/
theorem homEquiv_restriction_zero (F : X.Modules) [F.IsQuasicoherent]
    (φ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ etaleSheaf F) :
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (baseChangeFinalIsTerminal g)).homEquiv _ _
      (((etaleAbelianInverseImageConstantIso.{u, u + 1} g).app
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, u + 1} g).map φ ≫ comparison g F) =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (finalObjIsTerminal X)).homEquiv _ _ φ ≫
        (unit g F).hom.app (op (finalObj X)) := by
  let adjC := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} (finalObjIsTerminal X)
  let adjg := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange g) AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology
  let adjY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    (baseChangeFinalIsTerminal g)
  have hc : ((etaleAbelianInverseImageConstantIso.{u, u + 1} g).app
      (AddCommGrpCat.of (ULift ℤ))).inv =
      (adjY.leftAdjointUniq (adjC.comp adjg)).hom.app (AddCommGrpCat.of (ULift ℤ)) := by
    unfold etaleAbelianInverseImageConstantIso
    rfl
  rw [hc, adjY.homEquiv_naturality_right]
  refine (congrArg (· ≫ ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((smallEtaleBaseChange g).obj (finalObj X)))).map
        ((etaleAbelianInverseImage.{u, u + 1} g).map φ ≫ comparison g F))
    (Adjunction.homEquiv_leftAdjointUniq_hom_app adjY (adjC.comp adjg)
      (AddCommGrpCat.of (ULift ℤ)))).trans ?_
  refine ((adjC.comp adjg).homEquiv_unit _ _ _).symm.trans ?_
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, adjg.homEquiv_naturality_left]
  have h2 : adjg.homEquiv _ _ (comparison g F) = unit g F := Equiv.apply_symm_apply _ _
  rw [h2, adjC.homEquiv_naturality_right]
  rfl

end Formula

section Sections

open Stacks.AlgebraicGeometry.SectionsBaseChange

/-- **Flat base change of sections, as a spanning statement.** For a cartesian square
`T' ⟶ X ⟶ S ⟵ S' ⟵ T'` with `S, S'` affine, `S' ⟶ S` flat and `X` quasi-compact and
quasi-separated, every section of the pullback of a quasi-coherent module to `T'` is a finite sum
of pullbacks of sections multiplied by functions coming from `S'`. -/
theorem mem_closure_pullbackSections {S S' X T' : Scheme.{u}} [IsAffine S] [IsAffine S']
    {iX : X ⟶ S} {q : S' ⟶ S} [Flat q] [CompactSpace X] [QuasiSeparatedSpace X]
    {p : T' ⟶ X} {k : T' ⟶ S'} (H : IsPullback p k iX q) (M : X.Modules) [M.IsQuasicoherent]
    (w : Γ((Scheme.Modules.pullback p).obj M, ⊤)) :
    w ∈ AddSubgroup.closure {v | ∃ (b : Γ(S', ⊤)) (a : Γ(M, ⊤)),
      v = smulHom _ (k.appTop b) (pullbackSectionsHom p M ⊤ ⊤ (le_preimage_top p ⊤) a)} := by
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange H M
  obtain ⟨t, rfl⟩ := e.surjective w
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul b a =>
    refine AddSubgroup.subset_closure ⟨b, a, ?_⟩
    rw [he]
    show (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b •
      (pullbackSectionsHom p M ⊤ ⊤ (le_preimage_top p ⊤) a :
        Γ((Scheme.Modules.pullback p).obj M, ⊤)) = _
    rw [appLE_top_top_eq_appTop]
    rfl
  | add t t' ht ht' => rw [map_add]; exact add_mem ht ht'

end Sections

section Spans

open Stacks.AlgebraicGeometry.SectionsBaseChange

variable {S S' X Y : Scheme.{u}} [IsAffine S] [IsAffine S'] {f : X ⟶ S} {q : S' ⟶ S} [Flat q]
  [CompactSpace X] [QuasiSeparatedSpace X] {g : Y ⟶ X} {h : Y ⟶ S'} (hpb : IsPullback g h f q)

/-- The base change of the final object of `X_étale` along `g`, as a scheme. -/
abbrev finalT (g : Y ⟶ X) : Scheme.{u} := ((baseChangeOver g).obj (finalObj X)).left

/-- Its projection to `X`. -/
abbrev finalP (g : Y ⟶ X) : finalT g ⟶ X := ((baseChangeCounit g).app (finalObj X)).left

/-- Its projection to `Y`. -/
abbrev finalQ (g : Y ⟶ X) : finalT g ⟶ Y := ((baseChangeOver g).obj (finalObj X)).hom

include hpb in
omit [IsAffine S] [IsAffine S'] [Flat q] [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- The cartesian square through the base change of the final object. -/
theorem isPullback_baseChangeFinal : IsPullback (finalP g) (finalQ g ≫ h) f q := by
  have h1 : IsPullback (pullback.fst (𝟙 X) g) (pullback.snd (𝟙 X) g) (𝟙 X) g :=
    IsPullback.of_hasPullback _ _
  have h2 := h1.paste_vert hpb
  rw [Category.id_comp] at h2
  exact h2

/-- The module `(X ⟶ X)^* ℱ` whose global sections are the sections of `ℱᵉ` over the final
object. -/
abbrev finalM (F : X.Modules) : X.Modules := (Scheme.Modules.pullback (𝟙 X)).obj F

/-- The first identification of pullbacks to the base change of the final object. -/
def finalIso₁ (F : X.Modules) :
    (Scheme.Modules.pullback (finalP g)).obj (finalM F) ≅
      (Scheme.Modules.pullback (finalQ g ≫ g)).obj F :=
  (Scheme.Modules.pullbackComp (finalP g) (𝟙 X)).app F ≪≫
    (Scheme.Modules.pullbackCongr (Over.w ((baseChangeCounit g).app (finalObj X)))).app F

/-- The second identification of pullbacks to the base change of the final object. -/
def finalIso₂ (F : X.Modules) :
    (Scheme.Modules.pullback (finalQ g)).obj ((Scheme.Modules.pullback g).obj F) ≅
      (Scheme.Modules.pullback (finalQ g ≫ g)).obj F :=
  (Scheme.Modules.pullbackComp (finalQ g) g).app F

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- Over the final object, the unit sends a global section `a` of `finalM F` to the image of its
pullback along `finalP g` under the identifications `finalIso₁` and `finalIso₂`. -/
theorem unit_app_final (F : X.Modules) [F.IsQuasicoherent] (a : Γ(finalM F, ⊤)) :
    ((unit g F).hom.app (op (finalObj X)) (ULift.up a)).down =
      (finalIso₂ F).inv.app ⊤ ((finalIso₁ F).hom.app ⊤
        (pullbackSectionsHom (finalP g) (finalM F) ⊤ ⊤ (le_preimage_top _ ⊤) a)) := by
  have e1 := pullbackSectionsMap_apply_eq F ((baseChangeCounit g).app (finalObj X))
    (le_preimage_top _ ⊤) a
  have e2 : ((unit g F).hom.app (op (finalObj X)) (ULift.up a)).down =
      ((Scheme.Modules.pullbackComp (finalQ g) g).inv.app F).app ⊤
        (pullbackSectionsMap F ((baseChangeCounit g).app (finalObj X)) a) := rfl
  rw [e2, e1]
  rfl

/-- The identification of sections over the base change of the final object. -/
def finalSectionsMap (F : X.Modules) [F.IsQuasicoherent] :
    Γ((Scheme.Modules.pullback (finalP g)).obj (finalM F), ⊤) →+
      (etaleSheaf ((Scheme.Modules.pullback g).obj F)).obj.obj
        (op ((smallEtaleBaseChange g).obj (finalObj X))) :=
  (AddEquiv.ulift.symm.toAddMonoidHom).comp
    (((finalIso₂ F).inv.app ⊤).hom.comp ((finalIso₁ F).hom.app ⊤).hom)

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- `finalSectionsMap F v` is `v` transported along `finalIso₁` and `finalIso₂`. -/
theorem finalSectionsMap_apply (F : X.Modules) [F.IsQuasicoherent]
    (v : Γ((Scheme.Modules.pullback (finalP g)).obj (finalM F), ⊤)) :
    finalSectionsMap F v = ULift.up ((finalIso₂ F).inv.app ⊤ ((finalIso₁ F).hom.app ⊤ v)) :=
  rfl

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- The map `finalSectionsMap F` is surjective. -/
theorem finalSectionsMap_surjective (F : X.Modules) [F.IsQuasicoherent] :
    Function.Surjective (finalSectionsMap (g := g) F) := by
  intro t
  refine ⟨(finalIso₁ F).inv.app ⊤ ((finalIso₂ F).hom.app ⊤ t.down), ?_⟩
  rw [finalSectionsMap_apply]
  refine ULift.ext ?_
  show ((finalIso₁ F).inv.app ⊤ ≫ (finalIso₁ F).hom.app ⊤ ≫ (finalIso₂ F).inv.app ⊤)
    ((finalIso₂ F).hom.app ⊤ t.down) = t.down
  rw [← Category.assoc, ← Scheme.Modules.Hom.comp_app, (finalIso₁ F).inv_hom_id,
    Scheme.Modules.Hom.id_app, Category.id_comp]
  show ((finalIso₂ F).hom.app ⊤ ≫ (finalIso₂ F).inv.app ⊤) t.down = t.down
  rw [← Scheme.Modules.Hom.comp_app, (finalIso₂ F).hom_inv_id]
  rfl

omit [IsAffine S'] [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- `finalSectionsMap F` carries the product of the pullback of `a` with the image of a global
section `b` of `S'` to the scalar action of `b` on the image of `a` under the unit. -/
theorem finalSectionsMap_smul (F : X.Modules) [F.IsQuasicoherent] (b : Γ(S', ⊤))
    (a : Γ(finalM F, ⊤)) :
    finalSectionsMap F (smulHom _ ((finalQ g ≫ h).appTop b)
        (pullbackSectionsHom (finalP g) (finalM F) ⊤ ⊤ (le_preimage_top _ ⊤) a)) =
      (etaleScalar ((Scheme.Modules.pullback g).obj F) (h.appTop b)).hom.app
        (op ((smallEtaleBaseChange g).obj (finalObj X)))
          ((unit g F).hom.app (op (finalObj X)) (ULift.up a)) := by
  refine Eq.trans ?_ (etaleScalar_app _ _ _ _).symm
  refine congrArg ULift.up ?_
  rw [unit_app_final]
  have hc : (finalQ g ≫ h).appTop b = (finalQ g).appTop (h.appTop b) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  have h1 := Scheme.Modules.Hom.app_smul (finalIso₁ F).hom ((finalQ g ≫ h).appTop b)
    (pullbackSectionsHom (finalP g) (finalM F) ⊤ ⊤ (le_preimage_top _ ⊤) a)
  have h2 := Scheme.Modules.Hom.app_smul (finalIso₂ F).inv ((finalQ g ≫ h).appTop b)
    ((finalIso₁ F).hom.app ⊤
      (pullbackSectionsHom (finalP g) (finalM F) ⊤ ⊤ (le_preimage_top _ ⊤) a))
  rw [hc] at h1 h2
  simp only [smulHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hc]
  exact (congrArg (ConcreteCategory.hom ((finalIso₂ F).inv.app ⊤)) h1).trans h2

include hpb in
/-- **The sections over the final object of `Y_étale` are spanned by the image of the base
change map.** -/
theorem mem_closure_unit (F : X.Modules) [F.IsQuasicoherent]
    (t : (etaleSheaf ((Scheme.Modules.pullback g).obj F)).obj.obj
      (op ((smallEtaleBaseChange g).obj (finalObj X)))) :
    t ∈ AddSubgroup.closure {v | ∃ (b : Γ(S', ⊤)) (s : (etaleSheaf F).obj.obj (op (finalObj X))),
      v = (etaleScalar ((Scheme.Modules.pullback g).obj F) (h.appTop b)).hom.app
        (op ((smallEtaleBaseChange g).obj (finalObj X)))
          ((unit g F).hom.app (op (finalObj X)) s)} := by
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (𝟙 X) F
  obtain ⟨w, rfl⟩ := finalSectionsMap_surjective (g := g) F t
  have hmem := mem_closure_pullbackSections (isPullback_baseChangeFinal hpb) (finalM F) w
  have hmap : finalSectionsMap F w ∈ (AddSubgroup.closure {v | ∃ (b : Γ(S', ⊤))
      (a : Γ(finalM F, ⊤)), v = smulHom _ ((finalQ g ≫ h).appTop b)
        (pullbackSectionsHom (finalP g) (finalM F) ⊤ ⊤ (le_preimage_top _ ⊤) a)}).map
      (finalSectionsMap F) := ⟨w, hmem, rfl⟩
  rw [AddMonoidHom.map_closure] at hmap
  refine AddSubgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨b, a, rfl⟩, rfl⟩
  exact ⟨b, ULift.up a, finalSectionsMap_smul F b a⟩

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [CompactSpace ↥X] [QuasiSeparatedSpace ↥X] in
/-- The base change map in degree zero, through the identification of `H⁰` with sections over
the final object. -/
theorem equiv₀_restriction (F : X.Modules) [F.IsQuasicoherent]
    (x : Sheaf.H.{w} (etaleSheaf F) 0) :
    Sheaf.H.equiv₀ _ (baseChangeFinalIsTerminal g) (restriction g F 0 x) =
      (unit g F).hom.app (op (finalObj X)) (Sheaf.H.equiv₀ _ (finalObjIsTerminal X) x) := by
  obtain ⟨φ, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  have h1 : restriction g F 0 (Ext.addEquiv₀.symm φ) = Ext.addEquiv₀.symm
      (((etaleAbelianInverseImageConstantIso.{u, u + 1} g).app
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, u + 1} g).map φ ≫ comparison g F) := by
    show ((Ext.mk₀ _).comp ((Ext.mk₀ φ).mapExactFunctor _) (zero_add 0)).comp _ (add_zero 0) = _
    rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]
    rfl
  rw [h1]
  show AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (baseChangeFinalIsTerminal g)).homEquiv _ _ (Ext.addEquiv₀ (Ext.addEquiv₀.symm _))) =
    (unit g F).hom.app (op (finalObj X)) (AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (finalObjIsTerminal X)).homEquiv _ _ (Ext.addEquiv₀ (Ext.addEquiv₀.symm φ))))
  rw [Ext.addEquiv₀.apply_symm_apply, Ext.addEquiv₀.apply_symm_apply, homEquiv_restriction_zero]
  rfl

include hpb in
/-- **The base change map spans in degree zero.** -/
theorem spans_zero (F : X.Modules) [F.IsQuasicoherent] :
    Spans.{w} g (fun b : Γ(S', ⊤) => h.appTop b) F 0 := by
  intro y
  let Φ := Sheaf.H.equiv₀ (etaleSheaf ((Scheme.Modules.pullback g).obj F))
    (baseChangeFinalIsTerminal g)
  let Φ0 := Sheaf.H.equiv₀ (etaleSheaf F) (finalObjIsTerminal X)
  have key : ∀ v ∈ AddSubgroup.closure {v | ∃ (b : Γ(S', ⊤))
      (s : (etaleSheaf F).obj.obj (op (finalObj X))),
      v = (etaleScalar ((Scheme.Modules.pullback g).obj F) (h.appTop b)).hom.app
        (op ((smallEtaleBaseChange g).obj (finalObj X)))
          ((unit g F).hom.app (op (finalObj X)) s)},
      Φ.symm v ∈ AddSubgroup.closure (scaledImage g (fun b : Γ(S', ⊤) => h.appTop b) F 0) := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨b, s, rfl⟩ := hv
      refine AddSubgroup.subset_closure ⟨b, Φ0.symm s, ?_⟩
      apply Φ.injective
      rw [AddEquiv.apply_symm_apply]
      have hn := Sheaf.H.equiv₀_naturality (baseChangeFinalIsTerminal g)
        (etaleScalar ((Scheme.Modules.pullback g).obj F) (h.appTop b))
        (restriction g F 0 (Φ0.symm s))
      refine Eq.trans ?_ hn
      rw [equiv₀_restriction, AddEquiv.apply_symm_apply]
    | zero => rw [map_zero]; exact zero_mem _
    | add v v' _ _ hv hv' => rw [map_add]; exact add_mem hv hv'
    | neg v _ hv => rw [map_neg]; exact neg_mem hv
  have := key _ (mem_closure_unit hpb F (Φ y))
  rwa [AddEquiv.symm_apply_apply] at this

end Spans

end AlgebraicGeometry.QcohEtale

end
