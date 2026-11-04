module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ZariskiCechComplex
public import StacksFrontier.CategoryTheory.Sites.CechComplexMap
public import StacksFrontier.CategoryTheory.Sites.CechSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.BaseChangedFamilyComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocalQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation

/-!
# The Zariski Čech complex of `𝐆_a` is a resolution on the small étale site

Let `X` be a scheme and `U : ι → X.Opens` a family of opens covering `X`. The Čech complex
`Stacks.ArtinSchreier.zariskiCechComplex X U` of the presheaf `V ↦ ι_{V,*} 𝐆_{a,V}`, augmented by
`𝐆_a`, is a resolution of `𝐆_a` by abelian sheaves on the small étale site of `X`.

Exactness is checked on the sections over the étale `X`-schemes `W` mapping into one of the `U_i`
(`Stacks.Sites.quasiIsoAt_of_quasiIsoAt_sections`); these cover every object. On sections over
`W` the complex is the Čech complex, for the family `U`, of the presheaf `V ↦ Γ(W ×_X V)` on the
opens of `X`, which is the direct image along `W ⟶ X` of the structure sheaf of `W`. Its degree
zero homology is `Γ(W)` because that presheaf is a sheaf for the Zariski topology of `X`
(`Stacks.CategoryTheory.CechComplex.isLimitAugmentationFork`), and it is exact in positive
degrees because restriction to `U_i ∩ V` is invertible when `W` maps into `U_i`
(`Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom`).

## Main results

* `Stacks.ArtinSchreier.quasiIso_zariskiCechAugmentation`: the augmentation is a
  quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechZero TopologicalSpace

universe u


namespace Stacks.ArtinSchreier

variable (X : Scheme.{u})

/-- Sections over an étale `X`-scheme `W`, as a functor on abelian sheaves. -/
abbrev etaleSections (W : X.Etale) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ (evaluation _ _).obj (op W)

/-- The presheaf `V ↦ Γ(W ×_X V)` on the opens of `X`: the sections over `W` of the presheaf
`V ↦ ι_{V,*} 𝐆_{a,V}`. -/
abbrev openSectionsPresheaf (W : X.Etale) : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  openDirectImagePresheaf X ⋙ etaleSections X W

section Pullback

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The morphism `Y ×_X V' ⟶ Y ×_X V` for opens `V' ≤ V` of `X`. -/
abbrev pullbackOpenMap {V' V : X.Opens} (h : V' ≤ V) : pullback g V'.ι ⟶ pullback g V.ι :=
  pullback.map g V'.ι g V.ι (𝟙 _) (X.homOfLE h) (𝟙 _) (by simp) (by simp)

/-- The map `Y ×_X V' ⟶ Y ×_X V` commutes with the first projections to `Y`. -/
theorem pullbackOpenMap_fst {V' V : X.Opens} (h : V' ≤ V) :
    pullbackOpenMap g h ≫ pullback.fst g V.ι = pullback.fst g V'.ι := by
  rw [pullback.lift_fst, Category.comp_id]

/-- The map `Y ×_X V' ⟶ Y ×_X V` followed by the second projection is the second projection
followed by the inclusion `V' ⟶ V`. -/
theorem pullbackOpenMap_snd {V' V : X.Opens} (h : V' ≤ V) :
    pullbackOpenMap g h ≫ pullback.snd g V.ι = pullback.snd g V'.ι ≫ X.homOfLE h :=
  pullback.lift_snd _ _ _

/-- For `V' = V`, the map `Y ×_X V ⟶ Y ×_X V` is the identity. -/
theorem pullbackOpenMap_id (V : X.Opens) : pullbackOpenMap g (le_refl V) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackOpenMap_fst, Category.id_comp]
  · rw [pullbackOpenMap_snd, Category.id_comp, X.homOfLE_rfl, Category.comp_id]

/-- For `V'' ≤ V' ≤ V`, the map `Y ×_X V'' ⟶ Y ×_X V` is the composite of `Y ×_X V'' ⟶ Y ×_X V'`
and `Y ×_X V' ⟶ Y ×_X V`. -/
theorem pullbackOpenMap_comp {V'' V' V : X.Opens} (h₁ : V'' ≤ V') (h₂ : V' ≤ V) :
    pullbackOpenMap g (h₁.trans h₂) = pullbackOpenMap g h₁ ≫ pullbackOpenMap g h₂ := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackOpenMap_fst, Category.assoc, pullbackOpenMap_fst, pullbackOpenMap_fst]
  · rw [pullbackOpenMap_snd, Category.assoc, pullbackOpenMap_snd, ← Category.assoc,
      pullbackOpenMap_snd, Category.assoc, X.homOfLE_homOfLE]

/-- **The presheaf `V ↦ Γ(Y ×_X V)` on the opens of `X`**, with values in abelian groups. -/
def pullbackSectionsPresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).obj (op (pullback g V.unop.ι))
  map h := (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullbackOpenMap g h.unop.le).op
  map_id V := by
    rw [show pullbackOpenMap g (𝟙 V).unop.le = 𝟙 _ from pullbackOpenMap_id g V.unop]
    exact (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map_id _
  map_comp h₁ h₂ := by
    rw [show pullbackOpenMap g (h₁ ≫ h₂).unop.le =
        pullbackOpenMap g h₂.unop.le ≫ pullbackOpenMap g h₁.unop.le from
      pullbackOpenMap_comp g h₂.unop.le h₁.unop.le, op_comp, Functor.map_comp]

/-- The structure sheaf of `Y` pushed forward to the opens of `X`, as a presheaf of abelian
groups. -/
abbrev structurePushforward : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Opens.map g.base).op ⋙ Y.presheaf ⋙ additiveCoefficients.{u, 0}

/-- `Y ×_X V' ⟶ Y ×_X V` against the identification of the fibre products with open
subschemes of `Y`. -/
theorem pullbackRestrictIsoRestrict_inv_comp_pullbackOpenMap {V' V : X.Opens} (h : V' ≤ V) :
    (pullbackRestrictIsoRestrict g V').inv ≫ pullbackOpenMap g h =
      Y.homOfLE ((Opens.map g.base).monotone h) ≫ (pullbackRestrictIsoRestrict g V).inv := by
  have hfst : ((pullbackRestrictIsoRestrict g V').inv ≫ pullbackOpenMap g h) ≫
      pullback.fst g V.ι = (Y.homOfLE ((Opens.map g.base).monotone h) ≫
        (pullbackRestrictIsoRestrict g V).inv) ≫ pullback.fst g V.ι := by
    rw [Category.assoc, Category.assoc, pullbackOpenMap_fst, pullbackRestrictIsoRestrict_inv_fst,
      pullbackRestrictIsoRestrict_inv_fst, Scheme.homOfLE_ι]
  refine pullback.hom_ext hfst ?_
  rw [← cancel_mono V.ι, Category.assoc, Category.assoc, ← pullback.condition,
    ← Category.assoc, ← Category.assoc, hfst]
  simp only [Category.assoc, pullback.condition]

/-- **`V ↦ Γ(Y ×_X V)` is the pushforward of the structure sheaf of `Y`.** -/
def pullbackSectionsPresheafIso : pullbackSectionsPresheaf g ≅ structurePushforward g :=
  NatIso.ofComponents (fun V ↦ additiveCoefficients.{u, 0}.mapIso
      ((Scheme.Γ.mapIso (pullbackRestrictIsoRestrict g V.unop).op).symm ≪≫
        Y.restrictFunctorΓ.app (op ((Opens.map g.base).obj V.unop))))
    (by
      intro V V' h
      change additiveCoefficients.{u, 0}.map (Scheme.Γ.map (pullbackOpenMap g h.unop.le).op) ≫
          additiveCoefficients.{u, 0}.map (Scheme.Γ.map
            (pullbackRestrictIsoRestrict g V'.unop).inv.op ≫
              Y.restrictFunctorΓ.hom.app (op ((Opens.map g.base).obj V'.unop))) =
        additiveCoefficients.{u, 0}.map (Scheme.Γ.map
            (pullbackRestrictIsoRestrict g V.unop).inv.op ≫
              Y.restrictFunctorΓ.hom.app (op ((Opens.map g.base).obj V.unop))) ≫
          additiveCoefficients.{u, 0}.map (Y.presheaf.map ((Opens.map g.base).map h.unop).op)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      have h1 : Scheme.Γ.map (pullbackOpenMap g h.unop.le).op ≫
          Scheme.Γ.map (pullbackRestrictIsoRestrict g V'.unop).inv.op =
          Scheme.Γ.map (pullbackRestrictIsoRestrict g V.unop).inv.op ≫
            Scheme.Γ.map (Y.homOfLE ((Opens.map g.base).monotone h.unop.le)).op := by
        rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
          pullbackRestrictIsoRestrict_inv_comp_pullbackOpenMap]
      have h2 : Scheme.Γ.map (Y.homOfLE ((Opens.map g.base).monotone h.unop.le)).op ≫
          Y.restrictFunctorΓ.hom.app (op ((Opens.map g.base).obj V'.unop)) =
          Y.restrictFunctorΓ.hom.app (op ((Opens.map g.base).obj V.unop)) ≫
            Y.presheaf.map ((Opens.map g.base).map h.unop).op :=
        Y.restrictFunctorΓ.hom.naturality ((Opens.map g.base).map h.unop).op
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm))))

end Pullback

section Sheaf

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X)

/-- The structure sheaf of a scheme, read as a presheaf of abelian groups on its opens, is a
sheaf. -/
theorem isSheaf_presheaf_comp_additiveCoefficients :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y) (Y.presheaf ⋙ additiveCoefficients.{u, 0}) := by
  refine Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _ ?_
  have h : Presieve.IsSheaf (Opens.grothendieckTopology Y)
      (Y.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ Y.presheaf (CategoryTheory.forget CommRingCat)).1
        Y.sheaf.cond)
  exact (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := Y.presheaf ⋙ additiveCoefficients.{u, 0} ⋙ CategoryTheory.forget AddCommGrpCat)
    (fun {_} => Equiv.ulift.symm) (fun _ _ _ _ => rfl)).1 h

/-- **`V ↦ Γ(Y ×_X V)` is a sheaf on the opens of `X`.** -/
theorem isSheaf_pullbackSectionsPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (pullbackSectionsPresheaf g) :=
  Presheaf.isSheaf_of_iso_iff (pullbackSectionsPresheafIso g) |>.2
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf g.base
      (isSheaf_presheaf_comp_additiveCoefficients (Y := Y)))

end Sheaf

section Split

variable {X} {Y : Scheme.{u}} (g : Y ⟶ X) {U₀ : X.Opens} (hU₀ : g ⁻¹ᵁ U₀ = ⊤)

include hU₀ in
/-- If `Y` maps into `U₀`, restriction from `Y ×_X V` to `Y ×_X (U₀ ⨯ V)` is invertible. -/
theorem isIso_pullbackSectionsPresheaf_map_snd (V : X.Opens) :
    IsIso ((pullbackSectionsPresheaf g).map (prod.snd : U₀ ⨯ V ⟶ V).op) := by
  have hle : (Opens.map g.base).obj V ≤ (Opens.map g.base).obj (U₀ ⨯ V) := by
    intro x hx
    have h₀ : g.base x ∈ U₀ := (hU₀ ▸ trivial : x ∈ g ⁻¹ᵁ U₀)
    exact (prod.lift (homOfLE (inf_le_left : U₀ ⊓ V ≤ U₀))
      (homOfLE (inf_le_right : U₀ ⊓ V ≤ V))).le ⟨h₀, hx⟩
  have : IsIso ((Opens.map g.base).map (prod.snd : U₀ ⨯ V ⟶ V)) :=
    ⟨homOfLE hle, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : IsIso ((structurePushforward g).map (prod.snd : U₀ ⨯ V ⟶ V).op) := by
    show IsIso ((Y.presheaf ⋙ additiveCoefficients.{u, 0}).map
      ((Opens.map g.base).map (prod.snd : U₀ ⨯ V ⟶ V)).op)
    infer_instance
  exact (NatIso.isIso_map_iff (pullbackSectionsPresheafIso g) _).2 this

/-- The second projections `U₀ ⨯ V ⟶ V`, natural in `V`. -/
def prodSndNatTrans (U₀ : X.Opens) : Over.star U₀ ⋙ Over.forget U₀ ⟶ 𝟭 X.Opens where
  app V := prod.snd
  naturality _ _ _ := Subsingleton.elim _ _

include hU₀ in
/-- If `Y` maps into `U₀`, the presheaf `V ↦ Γ(Y ×_X V)` is its restriction along
`V ↦ U₀ ⨯ V`. -/
theorem isIso_whiskerRight_prodSnd :
    IsIso (Functor.whiskerRight (NatTrans.op (prodSndNatTrans U₀)) (pullbackSectionsPresheaf g)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun V ↦
    isIso_pullbackSectionsPresheaf_map_snd g hU₀ V.unop

end Split

section Resolution

variable {ι : Type} (U : ι → X.Opens)

/-- The étale `X`-schemes mapping into one of the members of the family `U`. -/
def MapsIntoMember (W : X.Etale) : Prop := ∃ i, W.hom ⁻¹ᵁ U i = ⊤

/-- **The étale `X`-schemes mapping into a member of an open covering cover every étale
`X`-scheme**: `W` is covered by the `W ×_X U_i`. -/
theorem coversByProperty_mapsIntoMember (hU : ⨆ i, U i = ⊤) :
    Stacks.Sites.CoversByProperty (MapsIntoMember X U) X.smallEtaleTopology := by
  intro W
  let Z : ι → X.Etale := fun i ↦ Scheme.Etale.mk (pullback.fst W.hom (U i).ι ≫ W.hom)
  let a : ∀ i, Z i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (pullback.fst W.hom (U i).ι) rfl
  have hcov : Sieve.ofArrows Z a ∈ X.smallEtaleTopology W := by
    refine (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2 (Set.eq_univ_of_forall fun x ↦ ?_)
    have hx : W.hom.base x ∈ ⨆ i, U i := hU ▸ trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    show x ∈ Set.range (pullback.fst W.hom (U i).ι)
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
    exact hi
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rintro V b ⟨_, g, _, ⟨i⟩, rfl⟩
  refine ⟨Z i, g, a i, ?_, rfl⟩
  refine ⟨i, top_unique fun y _ ↦ ?_⟩
  show (pullback.fst W.hom (U i).ι ≫ W.hom).base y ∈ U i
  rw [pullback.condition]
  exact (U i).range_ι.le (Set.mem_range_self _)

/-- The inclusion `V ⟶ X` of an open subscheme with `V = ⊤` is an isomorphism. -/
theorem isIso_ι_of_eq_top {V : X.Opens} (hV : V = ⊤) : IsIso V.ι := by
  subst hV
  exact inferInstanceAs (IsIso X.topIso.hom)

/-- **Degree zero of the Zariski Čech resolution, on the sections over an étale `X`-scheme.**
On sections over `W`, `Γ(W) ⟶ Č⁰ ⟶ Č¹` is the restriction of a function on `W` to the members of
the open covering `W ×_X U_i` followed by the Čech differential, which is exact and injective
on the left because `V ↦ Γ(W ×_X V)` is a sheaf on the opens of `X`. -/
theorem quasiIsoAt_zero_sections_zariskiCechAugmentation (hU : ⨆ i, U i = ⊤) (W : X.Etale) :
    QuasiIsoAt ((((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op W))).mapHomologicalComplex _).map
        (zariskiCechAugmentation X U)) 0 := by
  have hcovO : Sieve.ofArrows U (fun i ↦ terminal.from (U i)) ∈
      Opens.grothendieckTopology X (⊤_ X.Opens) := by
    have h := Stacks.Cohomology.CechZero.ofArrows_mem_grothendieckTopology U (⊤_ X.Opens)
      (fun i ↦ (terminal.from (U i)).le)
      (by rw [Stacks.CategoryTheory.CechComplex.terminal_eq_top, hU])
    convert h using 2
    exact funext fun _ ↦ Subsingleton.elim _ _
  have hlim := isLimitAugmentationFork U (pullbackSectionsPresheaf W.hom)
    (Opens.grothendieckTopology X) (isSheaf_pullbackSectionsPresheaf W.hom) hcovO
  have := isIso_ι_of_eq_top X (Stacks.CategoryTheory.CechComplex.terminal_eq_top (L := X.Opens))
  have hmono : Mono (aug U (pullbackSectionsPresheaf W.hom) terminalIsTerminal) :=
    Fork.IsLimit.mono hlim
  have hex : (ShortComplex.mk _ _ (aug_comp_d U (pullbackSectionsPresheaf W.hom)
      terminalIsTerminal)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hlim
  let F := etaleSections X W
  let e := mapCechIso F U (openDirectImagePresheaf X)
  have hcomp : F.map (zariskiCechAugmentationZero X U) ≫ e.hom.f 0 =
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullback.fst W.hom (⊤_ X.Opens).ι).op ≫
        aug U (pullbackSectionsPresheaf W.hom) terminalIsTerminal := by
    refine hom_ext U (pullbackSectionsPresheaf W.hom) fun x ↦ ?_
    have h1 := mapCechIso_hom_f_comp_π F U (openDirectImagePresheaf X) 0 x
    have h2 := (Category.assoc (openDirectImageUnit X (⊤_ X.Opens))
      (aug U (openDirectImagePresheaf X) terminalIsTerminal)
      (π U (openDirectImagePresheaf X) 0 x)).trans
        (congrArg (openDirectImageUnit X (⊤_ X.Opens) ≫ ·)
          (aug_comp_π U (openDirectImagePresheaf X) terminalIsTerminal x))
    have h3 := aug_comp_π U (pullbackSectionsPresheaf W.hom) terminalIsTerminal x
    exact (Category.assoc _ _ _).trans ((congrArg (F.map (zariskiCechAugmentationZero X U) ≫ ·)
      h1).trans ((F.map_comp _ _).symm.trans ((congrArg F.map h2).trans ((F.map_comp _ _).trans
        ((congrArg (_ ≫ ·) h3.symm).trans (Category.assoc _ _ _).symm)))))
  let u : F.obj (additiveSheaf.{u, 0} X) ≅ (pullbackSectionsPresheaf W.hom).obj (op (⊤_ X.Opens)) :=
    (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).mapIso (asIso (pullback.fst W.hom (⊤_ X.Opens).ι)).op
  have h0 : ((F.mapHomologicalComplex _).obj
      ((CochainComplex.single₀ _).obj (additiveSheaf.{u, 0} X))).d 0 0 = 0 :=
    HomologicalComplex.shape _ 0 0 (by simp)
  have h1 : ((F.mapHomologicalComplex _).obj
      ((CochainComplex.single₀ _).obj (additiveSheaf.{u, 0} X))).d 0 1 = 0 := by
    rw [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.single_obj_d, F.map_zero]
  have h2 : ((F.mapHomologicalComplex _).obj (zariskiCechComplex X U)).d 0 0 = 0 :=
    HomologicalComplex.shape _ 0 0 (by simp)
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ h0 h1 h2]
  have hf : (((F.mapHomologicalComplex _).map (zariskiCechAugmentation X U))).f 0 =
      F.map (zariskiCechAugmentationZero X U) := by
    rw [Functor.mapHomologicalComplex_map_f, zariskiCechAugmentation_f_zero]
    rfl
  let S₁ : ShortComplex AddCommGrpCat.{u + 1} :=
    ShortComplex.mk (u.hom ≫ aug U (pullbackSectionsPresheaf W.hom) terminalIsTerminal)
      (((cechComplexFunctor U).obj (pullbackSectionsPresheaf W.hom)).d 0 1)
      (by rw [Category.assoc, aug_comp_d, comp_zero])
  let S₂ : ShortComplex AddCommGrpCat.{u + 1} :=
    ShortComplex.mk _ _ (aug_comp_d U (pullbackSectionsPresheaf W.hom) terminalIsTerminal)
  have iso : S₁ ≅ S₂ := ShortComplex.isoMk u (Iso.refl _) (Iso.refl _)
    (Category.comp_id _).symm ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hS : S₁.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
  let S₀ : ShortComplex AddCommGrpCat.{u + 1} :=
    ShortComplex.mk (((F.mapHomologicalComplex _).map (zariskiCechAugmentation X U)).f 0)
      (((F.mapHomologicalComplex _).obj (zariskiCechComplex X U)).d 0 1)
      (by rw [HomologicalComplex.Hom.comm, h1, zero_comp])
  have iso' : S₀ ≅ S₁ := ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.Hom.isoApp e 0)
    (HomologicalComplex.Hom.isoApp e 1)
    ((Category.id_comp _).trans (hcomp.symm.trans (congrArg (· ≫ e.hom.f 0) hf.symm)))
    (e.hom.comm 0 1)
  refine ⟨(ShortComplex.exact_iff_of_iso iso').2 hS, ?_⟩
  show Mono (((F.mapHomologicalComplex _).map (zariskiCechAugmentation X U)).f 0)
  rw [hf]
  have hm : Mono ((Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
      (pullback.fst W.hom (⊤_ X.Opens).ι).op ≫
        aug U (pullbackSectionsPresheaf W.hom) terminalIsTerminal) :=
    @mono_comp _ _ _ _ _ _ inferInstance _ hmono
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hm hcomp

/-- **The Zariski Čech complex of `𝐆_a` for an open covering is a resolution of `𝐆_a`** on the
small étale site. -/
theorem quasiIso_zariskiCechAugmentation (hU : ⨆ i, U i = ⊤) :
    QuasiIso (zariskiCechAugmentation X U) := by
  refine ⟨fun n ↦ Stacks.Sites.quasiIsoAt_of_quasiIsoAt_sections
    (coversByProperty_mapsIntoMember X U hU) (zariskiCechAugmentation X U) n ?_⟩
  rintro W ⟨i₀, hi₀⟩
  have e : ((etaleSections X W).mapHomologicalComplex _).obj (zariskiCechComplex X U) ≅
      (cechComplexFunctor U).obj (pullbackSectionsPresheaf W.hom) :=
    mapCechIso (etaleSections X W) U (openDirectImagePresheaf X)
  cases n with
  | succ m =>
    have h1 := Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom U (U i₀)
      (pullbackSectionsPresheaf W.hom) (𝟙 (U i₀)) (m + 1) (by omega)
    have := isIso_whiskerRight_prodSnd W.hom hi₀
    have e1 : (cechComplexFunctor U).obj ((Over.star (U i₀) ⋙ Over.forget (U i₀)).op ⋙
        pullbackSectionsPresheaf W.hom) ≅
        (cechComplexFunctor U).obj (pullbackSectionsPresheaf W.hom) :=
      (cechComplexFunctor U).mapIso (asIso (Functor.whiskerRight
        (NatTrans.op (prodSndNatTrans (U i₀))) (pullbackSectionsPresheaf W.hom))).symm
    have hK : (((etaleSections X W).mapHomologicalComplex _).obj
        ((CochainComplex.single₀ _).obj (additiveSheaf.{u, 0} X))).ExactAt (m + 1) :=
      (HomologicalComplex.exactAt_iff _ _).2 (ShortComplex.exact_of_isZero_X₂ _
        ((etaleSections X W).map_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))))
    exact (quasiIsoAt_iff_exactAt _ _ hK).2 ((h1.of_iso e1).of_iso e.symm)
  | zero => exact quasiIsoAt_zero_sections_zariskiCechAugmentation X U hU W

end Resolution

end Stacks.ArtinSchreier

end
