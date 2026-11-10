module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.SplitLocal

/-!
# The fpqc-local description of the coequalizers of `FÉt_X`

Let `X` be a scheme and let `a, b : Y ⟶ Z` be two morphisms of finite étale covers of `X`. This
file constructs the fpqc covering of the coequalizer that Stacks Tag 0BNA asks for, and so proves
`Stacks.FundamentalGroup.HasFiniteColimitsWithLocalCoequalizers X` for every scheme `X`.

Around any point of `X` the two covers become disjoint unions of copies of the base, by Stacks
Tag 04HN applied twice; shrinking the resulting étale neighbourhood to a Zariski-open
neighbourhood makes the two morphisms induced by maps of the index sets. The shrinking is
possible because each component of a morphism of split covers is a section of the fold map, a
section hits a single copy near any given point, and there are only finitely many components.
Over the resulting neighbourhood the coequalizer is the split cover indexed by the coequalizer of
the index maps, and its underlying cofork of schemes is a coequalizer; this persists after any
further flat base change, because base change takes split covers to split covers and
index-induced morphisms to index-induced morphisms.

The covering of the coequalizer is then obtained by pulling these neighbourhoods back along the
structure morphism of the coequalizer. Its pairwise overlaps are again base changes of the same
shape, along the fibre products of the neighbourhoods over `X`, which is why the overlap clause of
Tag 0BMN comes out of the same statement.

## Main results

* `Stacks.FundamentalGroup.comp_eq_sigmaι_of_le` — on an open set over which a section of the
  fold map of a split cover hits the `i`-th component, that section *is* the `i`-th inclusion.
* `Stacks.FundamentalGroup.exists_isOpen_splitCoverMap_baseChange` — **the Zariski refinement**:
  two morphisms of split covers become index-induced over a small enough open neighbourhood of
  any point.
* `Stacks.FundamentalGroup.exists_isOpen_splitData` and
  `Stacks.FundamentalGroup.splitData_comp` — the trivialization over the refined neighbourhood,
  and its stability under further base change.
* `Stacks.FundamentalGroup.exists_etale_isColimit_baseChangeCofork` — the étale-local
  trivialization of Tag 0BNA, in the form the covering consumes.
* `Stacks.FundamentalGroup.isPullback_overlap` — an overlap of two base-changed étale
  neighbourhoods is itself such a base change.
* `Stacks.FundamentalGroup.hasFiniteColimitsWithLocalCoequalizers` — **the coequalizers of
  `FÉt_X` are coequalizers of schemes over an fpqc covering of their target and over its pairwise
  overlaps.**

## References

* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
* [Stacks Project, Tag 0BMN](https://stacks.math.columbia.edu/tag/0BMN)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.FundamentalGroup

/-! ### Transporting a morphism along isomorphisms -/

section Transport

universe v₁ v₂ u₁ u₂

/-- Transporting a morphism along isomorphisms of its source and target through a functor: if
the coordinates of `f` in the isomorphic objects are carried by a further pair of isomorphisms
to `g`, then `g` is the transport of `F.map f`. -/
theorem mapIso_trans_hom_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B A' B' : C} {A'' B'' : D} (f : A ⟶ B) (eY : A ≅ A') (eZ : B ≅ B')
    (jY : F.obj A' ≅ A'') (jZ : F.obj B' ≅ B'') (g : A'' ⟶ B'')
    (hg : jY.hom ≫ g = F.map (eY.inv ≫ f ≫ eZ.hom) ≫ jZ.hom) :
    (F.mapIso eY ≪≫ jY).hom ≫ g = F.map f ≫ (F.mapIso eZ ≪≫ jZ).hom := by
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Category.assoc,
    hg, ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc, Functor.map_comp_assoc]

/-- Transporting a morphism along a natural isomorphism of functors. -/
theorem natIsoApp_trans_hom_comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {K L : C ⥤ D} (α : K ≅ L) {A B : C} {A'' B'' : D} (f : A ⟶ B)
    (EY : L.obj A ≅ A'') (EZ : L.obj B ≅ B'') (g : A'' ⟶ B'')
    (hg : EY.hom ≫ g = L.map f ≫ EZ.hom) :
    (α.app A ≪≫ EY).hom ≫ g = K.map f ≫ (α.app B ≪≫ EZ).hom := by
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, hg, NatTrans.naturality_assoc]

end Transport

/-! ### A section of a split cover lands in one copy locally -/

section Section

variable {P : Scheme.{u}} {ι : Type u}

/-- A section of the fold map of a split cover hits some component at each point of the base. -/
theorem exists_mem_preimage_opensRange (s : P ⟶ ∐ fun _ : ι => P) (u : P) :
    ∃ i : ι, u ∈ s ⁻¹ᵁ (Sigma.ι (fun _ : ι => P) i).opensRange := by
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk (fun _ : ι => P)).surjective (s.base u)
  exact ⟨i, y, by simpa using hy⟩

/-- On an open set over which a section of the fold map hits the `i`-th component, that section
*is* the `i`-th inclusion. -/
theorem comp_eq_sigmaι_of_le (s : P ⟶ ∐ fun _ : ι => P)
    (hs : s ≫ Sigma.desc (fun _ : ι => 𝟙 P) = 𝟙 P) (i : ι) (V : P.Opens)
    (hV : V ≤ s ⁻¹ᵁ (Sigma.ι (fun _ : ι => P) i).opensRange) :
    V.ι ≫ s = V.ι ≫ Sigma.ι (fun _ : ι => P) i := by
  have hrange : Set.range (V.ι ≫ s).base ⊆ Set.range (Sigma.ι (fun _ : ι => P) i).base := by
    rintro x ⟨v, rfl⟩
    exact hV v.2
  have hfac := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : ι => P) i) (V.ι ≫ s) hrange
  have hid : IsOpenImmersion.lift (Sigma.ι (fun _ : ι => P) i) (V.ι ≫ s) hrange = V.ι := by
    rw [← Category.comp_id (IsOpenImmersion.lift _ _ _), ← Sigma.ι_comp_desc (fun _ : ι => 𝟙 P) i,
      ← Category.assoc, hfac, Category.assoc, hs, Category.comp_id]
  exact hfac.symm.trans (congrArg (fun t => t ≫ Sigma.ι (fun _ : ι => P) i) hid)

end Section

/-! ### Index-induced morphisms after a Zariski refinement -/

section Induced

variable {P V : Scheme.{u}} (h : V ⟶ P) {ι κ : Type u} [Finite ι] [Finite κ]
  (w : splitCover P κ ⟶ splitCover P ι) (σ : κ → ι)

/-- **If over `h` each component of a morphism of split covers lands in a single copy, then the
base change of that morphism along `h` is induced by the resulting map of index types.** -/
theorem splitCoverBaseChangeIso_hom_comp_splitCoverMap
    (hσ : ∀ j, h ≫ Sigma.ι (fun _ : κ => P) j ≫ w.left =
      h ≫ Sigma.ι (fun _ : ι => P) (σ j)) :
    (splitCoverBaseChangeIso h κ).hom ≫ splitCoverMap V σ =
      (finiteEtaleBaseChange h).map w ≫ (splitCoverBaseChangeIso h ι).hom := by
  refine MorphismProperty.Over.Hom.ext ?_
  change (splitCoverPullbackIso h κ).hom ≫ sigmaIndexMap V σ =
    ((Over.pullback h).map ((finiteEtaleOverForgetOver P).map w)).left ≫
      (splitCoverPullbackIso h ι).hom
  have hfst : ∀ b : κ, Sigma.ι (fun _ : κ => V) b ≫ (splitCoverPullbackIso h κ).inv ≫
        pullback.fst ((finiteEtaleOverForgetOver P).obj (splitCover P κ)).hom h ≫
          ((finiteEtaleOverForgetOver P).map w).left =
      Sigma.ι (fun _ : κ => V) b ≫ sigmaIndexMap V σ ≫ (splitCoverPullbackIso h ι).inv ≫
        pullback.fst ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h := by
    intro b
    rw [splitCoverPullbackIso_inv_fst_assoc, ι_sigmaIndexMap_assoc,
      splitCoverPullbackIso_inv_fst]
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ ((finiteEtaleOverForgetOver P).map w).left)
      (Sigma.ι_comp_desc (fun i : κ => h ≫ Sigma.ι (fun _ : κ => P) i) b)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (hσ b) ?_
    exact (Sigma.ι_comp_desc (fun i : ι => h ≫ Sigma.ι (fun _ : ι => P) i) (σ b)).symm
  have key : (splitCoverPullbackIso h κ).inv ≫
      ((Over.pullback h).map ((finiteEtaleOverForgetOver P).map w)).left =
        sigmaIndexMap V σ ≫ (splitCoverPullbackIso h ι).inv := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
      exact Sigma.hom_ext _ _ hfst
    · simp only [Category.assoc, baseChange_left_comp_snd]
      refine Sigma.hom_ext _ _ fun j => ?_
      simp [ι_sigmaIndexMap_assoc]
  simpa using congrArg (fun t => (splitCoverPullbackIso h κ).hom ≫ t ≫
    (splitCoverPullbackIso h ι).hom) key.symm

end Induced

/-! ### The Zariski refinement -/

section Refinement

variable {P : Scheme.{u}} {ι κ : Type u} [Finite ι] [Finite κ]

/-- Each component of a morphism of split covers is a section of the fold map. -/
theorem comp_splitCover_hom (w : splitCover P κ ⟶ splitCover P ι) (j : κ) :
    (Sigma.ι (fun _ : κ => P) j ≫ w.left) ≫ Sigma.desc (fun _ : ι => 𝟙 P) = 𝟙 P := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => Sigma.ι (fun _ : κ => P) j ≫ t)
    (MorphismProperty.Over.w w)) ?_
  exact Sigma.ι_comp_desc (fun _ : κ => 𝟙 P) j

/-- **The Zariski refinement of Stacks Tag 0BNA.** Two morphisms of split finite étale covers of
`P` become induced by maps of the index types over a small enough open neighbourhood of any point
of `P`. -/
theorem exists_isOpen_splitCoverMap_baseChange (wa wb : splitCover P κ ⟶ splitCover P ι)
    (u : P) :
    ∃ (V : P.Opens) (_ : u ∈ V) (σ τ : κ → ι),
      ((splitCoverBaseChangeIso V.ι κ).hom ≫ splitCoverMap V.toScheme σ =
          (finiteEtaleBaseChange V.ι).map wa ≫ (splitCoverBaseChangeIso V.ι ι).hom) ∧
        ((splitCoverBaseChangeIso V.ι κ).hom ≫ splitCoverMap V.toScheme τ =
          (finiteEtaleBaseChange V.ι).map wb ≫ (splitCoverBaseChangeIso V.ι ι).hom) := by
  have key : ∀ w : splitCover P κ ⟶ splitCover P ι, ∃ (W : P.Opens) (_ : u ∈ W) (σ : κ → ι),
      ∀ V : P.Opens, V ≤ W → (splitCoverBaseChangeIso V.ι κ).hom ≫ splitCoverMap V.toScheme σ =
        (finiteEtaleBaseChange V.ι).map w ≫ (splitCoverBaseChangeIso V.ι ι).hom := by
    intro w
    choose σ hσ using fun j : κ =>
      exists_mem_preimage_opensRange (Sigma.ι (fun _ : κ => P) j ≫ w.left) u
    refine ⟨⟨⋂ j : κ, (((Sigma.ι (fun _ : κ => P) j ≫ w.left) ⁻¹ᵁ
      (Sigma.ι (fun _ : ι => P) (σ j)).opensRange : P.Opens) : Set P),
      isOpen_iInter_of_finite fun j => Opens.isOpen _⟩, Set.mem_iInter.2 hσ, σ, fun V hV => ?_⟩
    exact splitCoverBaseChangeIso_hom_comp_splitCoverMap _ w σ fun j =>
      comp_eq_sigmaι_of_le _ (comp_splitCover_hom w j) (σ j) _ fun x hx =>
        Set.mem_iInter.1 (hV hx) j
  obtain ⟨Wa, hua, σ, hσ⟩ := key wa
  obtain ⟨Wb, hub, τ, hτ⟩ := key wb
  exact ⟨Wa ⊓ Wb, ⟨hua, hub⟩, σ, τ, hσ _ inf_le_left, hτ _ inf_le_right⟩

end Refinement

/-! ### Trivializing both covers and both morphisms at once -/

section Trivialize

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X} {U : Scheme.{u}} (h : U ⟶ X)
  {ι κ : Type u} [Finite ι] [Finite κ]
  (eY : (finiteEtaleBaseChange h).obj Y ≅ splitCover U κ)
  (eZ : (finiteEtaleBaseChange h).obj Z ≅ splitCover U ι)

/-- The transported trivializations turn an index-induced base change into an index-induced
description of the original morphism. -/
theorem splitData_aux (a : Y ⟶ Z) (V : U.Opens) (σ : κ → ι)
    (hA : (splitCoverBaseChangeIso V.ι κ).hom ≫ splitCoverMap V.toScheme σ =
      (finiteEtaleBaseChange V.ι).map (eY.inv ≫ (finiteEtaleBaseChange h).map a ≫ eZ.hom) ≫
        (splitCoverBaseChangeIso V.ι ι).hom) :
    ((MorphismProperty.Over.pullbackComp V.ι h).app Y ≪≫
        (finiteEtaleBaseChange V.ι).mapIso eY ≪≫ splitCoverBaseChangeIso V.ι κ).hom ≫
        splitCoverMap V.toScheme σ =
      (finiteEtaleBaseChange (V.ι ≫ h)).map a ≫
        ((MorphismProperty.Over.pullbackComp V.ι h).app Z ≪≫
          (finiteEtaleBaseChange V.ι).mapIso eZ ≪≫ splitCoverBaseChangeIso V.ι ι).hom :=
  natIsoApp_trans_hom_comp (MorphismProperty.Over.pullbackComp V.ι h) a _ _ _
    (mapIso_trans_hom_comp (finiteEtaleBaseChange V.ι) ((finiteEtaleBaseChange h).map a)
      eY eZ _ _ _ hA)

include eY eZ in
/-- **Over a suitable open subset of an étale neighbourhood trivializing both covers, both
morphisms become induced by maps of the index types.** -/
theorem exists_isOpen_splitData (a b : Y ⟶ Z) (u : U) :
    ∃ (V : U.Opens) (_ : u ∈ V) (σ τ : κ → ι)
      (eY' : (finiteEtaleBaseChange (V.ι ≫ h)).obj Y ≅ splitCover V.toScheme κ)
      (eZ' : (finiteEtaleBaseChange (V.ι ≫ h)).obj Z ≅ splitCover V.toScheme ι),
      eY'.hom ≫ splitCoverMap V.toScheme σ =
          (finiteEtaleBaseChange (V.ι ≫ h)).map a ≫ eZ'.hom ∧
        eY'.hom ≫ splitCoverMap V.toScheme τ =
          (finiteEtaleBaseChange (V.ι ≫ h)).map b ≫ eZ'.hom := by
  obtain ⟨V, huV, σ, τ, hA, hB⟩ := exists_isOpen_splitCoverMap_baseChange
    (eY.inv ≫ (finiteEtaleBaseChange h).map a ≫ eZ.hom)
    (eY.inv ≫ (finiteEtaleBaseChange h).map b ≫ eZ.hom) u
  refine ⟨V, huV, σ, τ,
    (MorphismProperty.Over.pullbackComp V.ι h).app Y ≪≫
      (finiteEtaleBaseChange V.ι).mapIso eY ≪≫ splitCoverBaseChangeIso V.ι κ,
    (MorphismProperty.Over.pullbackComp V.ι h).app Z ≪≫
      (finiteEtaleBaseChange V.ι).mapIso eZ ≪≫ splitCoverBaseChangeIso V.ι ι, ?_, ?_⟩
  · exact splitData_aux h eY eZ a V σ hA
  · exact splitData_aux h eY eZ b V τ hB

/-- **Split data is stable under further base change**: base change takes split covers to split
covers and index-induced morphisms to index-induced morphisms. -/
theorem splitData_comp (a : Y ⟶ Z) {U' : Scheme.{u}} (k : U' ⟶ U) (σ : κ → ι)
    (hσ : eY.hom ≫ splitCoverMap U σ = (finiteEtaleBaseChange h).map a ≫ eZ.hom) :
    ((MorphismProperty.Over.pullbackComp k h).app Y ≪≫
        (finiteEtaleBaseChange k).mapIso eY ≪≫ splitCoverBaseChangeIso k κ).hom ≫
        splitCoverMap U' σ =
      (finiteEtaleBaseChange (k ≫ h)).map a ≫
        ((MorphismProperty.Over.pullbackComp k h).app Z ≪≫
          (finiteEtaleBaseChange k).mapIso eZ ≪≫ splitCoverBaseChangeIso k ι).hom := by
  have hw : eY.inv ≫ (finiteEtaleBaseChange h).map a ≫ eZ.hom = splitCoverMap U σ := by
    rw [← hσ]
    exact Iso.inv_hom_id_assoc eY _
  refine natIsoApp_trans_hom_comp (MorphismProperty.Over.pullbackComp k h) a _ _ _
    (mapIso_trans_hom_comp (finiteEtaleBaseChange k) ((finiteEtaleBaseChange h).map a)
      eY eZ _ _ _ ?_)
  rw [hw]
  exact splitCoverBaseChangeIso_comp k ι σ

end Trivialize

/-! ### Base change of the coequalizer itself -/

section BaseChangeComp

variable {X P : Scheme.{u}} (g : P ⟶ X) {Y Z : FiniteEtaleOver X} {a b : Y ⟶ Z}
  {ι κ : Type u} [Finite ι] [Finite κ] {σ τ : κ → ι}
  {eY : (finiteEtaleBaseChange g).obj Y ≅ splitCover P κ}
  {eZ : (finiteEtaleBaseChange g).obj Z ≅ splitCover P ι}

/-- **Over a flat base change on which both covers split and both morphisms are index-induced,
the coequalizer stays a coequalizer after any further base change.** -/
def isColimitCoforkBaseChangeComp [Flat g] (c : Cofork a b) (hc : IsColimit c)
    (ha : eY.hom ≫ splitCoverMap P σ = (finiteEtaleBaseChange g).map a ≫ eZ.hom)
    (hb : eY.hom ≫ splitCoverMap P τ = (finiteEtaleBaseChange g).map b ≫ eZ.hom)
    {P' : Scheme.{u}} (k : P' ⟶ P) :
    IsColimit (Cofork.ofπ ((finiteEtaleBaseChange (k ≫ g)).map c.π)
      (comp_map_cofork_π (k ≫ g) a b c)) := by
  have hcP := isColimitCoforkBaseChange g a b c hc
  have hsp := isColimitSplitCoforkOfIso g ha hb
  have hw : eZ.hom ≫ splitCoverMap P (toIndexCoeq σ τ) =
      (finiteEtaleBaseChange g).map c.π ≫ (hcP.coconePointUniqueUpToIso hsp).hom :=
    (hcP.comp_coconePointUniqueUpToIso_hom hsp WalkingParallelPair.one).symm
  have hπ' := splitData_comp g eZ (hcP.coconePointUniqueUpToIso hsp) c.π k (toIndexCoeq σ τ) hw
  refine Cofork.isColimitOfIsos (splitCoverCofork P' σ τ) (isColimit_splitCoverCofork P' σ τ) _
    (((MorphismProperty.Over.pullbackComp k g).app Y ≪≫
      (finiteEtaleBaseChange k).mapIso eY ≪≫ splitCoverBaseChangeIso k κ).symm)
    (((MorphismProperty.Over.pullbackComp k g).app Z ≪≫
      (finiteEtaleBaseChange k).mapIso eZ ≪≫ splitCoverBaseChangeIso k ι).symm)
    (((MorphismProperty.Over.pullbackComp k g).app c.pt ≪≫
      (finiteEtaleBaseChange k).mapIso (hcP.coconePointUniqueUpToIso hsp) ≪≫
        splitCoverBaseChangeIso k (IndexCoeq σ τ)).symm)
    (inv_comp_map_baseChange (k ≫ g) (splitData_comp g eY eZ a k σ ha))
    (inv_comp_map_baseChange (k ≫ g) (splitData_comp g eY eZ b k τ hb)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ _) hπ') ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => (finiteEtaleBaseChange (k ≫ g)).map c.π ≫ t)
    (Iso.hom_inv_id _)) ?_
  exact Category.comp_id _

end BaseChangeComp

/-! ### The étale-local trivialization -/

section Etale

/-- **The étale-local trivialization of Stacks Tag 0BNA.** Around every point of `X` there is an
étale neighbourhood over which both covers split and both morphisms are induced by maps of the
index types; consequently the underlying cofork of schemes of any coequalizer of the two
morphisms is a coequalizer after base change to that neighbourhood, and to any further flat base
change of it. -/
theorem exists_etale_isColimit_baseChangeCofork {X : Scheme.{u}} {Y Z : FiniteEtaleOver X}
    (a b : Y ⟶ Z) (x : X) :
    ∃ (P : Scheme.{u}) (g : P ⟶ X) (_ : Etale g) (p : P), g p = x ∧
      (∀ (P' : Scheme.{u}) (k : P' ⟶ P) (g' : P' ⟶ X), Flat k → g' = k ≫ g →
        ∀ (c : Cofork a b), IsColimit c → ∀ {S : Scheme.{u}} (s : S ⟶ c.pt.left) (q : S ⟶ P'),
          IsPullback s q c.pt.hom g' →
            Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
              (congrArg (fun t => t.left) c.condition) s))) ∧
        ∀ (P' : Scheme.{u}) (k : P' ⟶ P) (g' : P' ⟶ X), g' = k ≫ g → ∀ (c : Cofork a b),
          IsColimit c → Nonempty (IsColimit (Cofork.ofπ ((finiteEtaleBaseChange g').map c.π)
            (comp_map_cofork_π g' a b c))) := by
  have hZf : IsFinite Z.hom := Z.prop.1
  have hZe : Etale Z.hom := Z.prop.2
  obtain ⟨U₁, h₁, hh₁, u₁, hu₁, hsZ₁⟩ := Stacks.Etale.exists_etale_isSplitCover Z.hom x
  have := hh₁
  have hYf : IsFinite (pullback.snd Y.hom h₁) := ((finiteEtaleBaseChange h₁).obj Y).prop.1
  have hYe : Etale (pullback.snd Y.hom h₁) := ((finiteEtaleBaseChange h₁).obj Y).prop.2
  obtain ⟨U₂, h₂, hh₂, u₂, hu₂, hsY₂⟩ :=
    Stacks.Etale.exists_etale_isSplitCover (pullback.snd Y.hom h₁) u₁
  have := hh₂
  obtain ⟨κ, hκ, eY0, heY0⟩ := (Stacks.Etale.isSplitCover_pullback_snd_comp Y.hom h₁ h₂).mp hsY₂
  obtain ⟨ι, hι, eZ0, heZ0⟩ := (Stacks.Etale.isSplitCover_pullback_snd_comp Z.hom h₁ h₂).mp
    (Stacks.Etale.isSplitCover_pullback_snd hsZ₁ h₂)
  have := hκ
  have := hι
  obtain ⟨V, huV, σ, τ, eY, eZ, ha, hb⟩ := exists_isOpen_splitData (h₂ ≫ h₁)
    (finiteEtaleOverIsoMk eY0 heY0) (finiteEtaleOverIsoMk eZ0 heZ0) a b u₂
  refine ⟨V.toScheme, V.ι ≫ (h₂ ≫ h₁), inferInstance, ⟨u₂, huV⟩, ?_, ?_, ?_⟩
  · change h₁.base (h₂.base u₂) = x
    rw [hu₂, hu₁]
  · intro P' k g' hk hg' c hc S s q hs
    subst hg'
    have := hk
    exact ⟨isColimitBaseChangeCoforkOfSplit (k ≫ V.ι ≫ (h₂ ≫ h₁)) c hc
      (splitData_comp (V.ι ≫ (h₂ ≫ h₁)) eY eZ a k σ ha)
      (splitData_comp (V.ι ≫ (h₂ ≫ h₁)) eY eZ b k τ hb) hs⟩
  · intro P' k g' hg' c hc
    subst hg'
    exact ⟨isColimitCoforkBaseChangeComp (V.ι ≫ (h₂ ≫ h₁)) c hc ha hb k⟩

end Etale

/-! ### The overlaps of the resulting covering -/

section Overlap

variable {W X : Scheme.{u}} (w : W ⟶ X) {P₁ P₂ : Scheme.{u}} (g₁ : P₁ ⟶ X) (g₂ : P₂ ⟶ X)

/-- The two projections of an overlap agree over the base. -/
theorem overlap_condition :
    (pullback.fst (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.snd w g₁) ≫ g₁ =
      (pullback.snd (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.snd w g₂) ≫ g₂ := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition,
    ← Category.assoc, ← Category.assoc, pullback.condition]

/-- **The overlap of two base-changed étale neighbourhoods is itself such a base change**, along
the fibre product of the two neighbourhoods. -/
theorem isPullback_overlap :
    IsPullback (pullback.fst (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.fst w g₁)
      (pullback.lift (pullback.fst (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.snd w g₁)
        (pullback.snd (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.snd w g₂)
        (overlap_condition w g₁ g₂)) w (pullback.fst g₁ g₂ ≫ g₁) := by
  have hs : IsPullback (pullback.fst (pullback.fst w g₁) (pullback.fst w g₂))
      (pullback.snd (pullback.fst w g₁) (pullback.fst w g₂) ≫ pullback.snd w g₂)
      (pullback.fst w g₁ ≫ w) g₂ :=
    (IsPullback.of_hasPullback _ _).paste_vert (IsPullback.of_hasPullback w g₂)
  refine IsPullback.paste_horiz (IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback g₁ g₂)) (IsPullback.of_hasPullback w g₁)
  rw [pullback.lift_snd, ← pullback.condition]
  exact hs

end Overlap

/-! ### The fpqc-local description of the coequalizers -/

/-- The category of finite étale covers of a scheme has finite colimits, and the underlying cofork
of schemes of a coequalizer of two morphisms of finite étale covers is a coequalizer over an fpqc
covering of its target and over each pairwise overlap of that covering. -/
@[stacks 0BN9 "finite colimits"]
instance hasFiniteColimitsWithLocalCoequalizers (X : Scheme.{u}) :
    HasFiniteColimitsWithLocalCoequalizers X :=
  { hasFiniteColimits_finiteEtaleOver X with
    exists_fpqcCover_isColimit_baseChangeCofork := by
      intro Y Z a b c hc
      choose P g hg p hp hloc using fun x : X => exists_etale_isColimit_baseChangeCofork a b x
      have hEt : ∀ x : X, Etale (pullback.fst c.pt.hom (g x)) := by
        intro x
        have := hg x
        infer_instance
      refine ⟨(Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) X
        (fun x => pullback c.pt.hom (g x)) (fun x => pullback.fst c.pt.hom (g x)) ?_
        (fun x => have := hEt x; ⟨inferInstance, inferInstance⟩)).weaken
          Scheme.fppfPrecoverage_le_fpqcPrecoverage, fun i => ?_, fun i j => ?_⟩
      · intro v
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.pt.hom)
          (g := g (c.pt.hom.base v)) v (p _) (hp _).symm
        exact ⟨c.pt.hom.base v, z, hz⟩
      · exact (hloc i).1 (P i) (𝟙 (P i)) (g i) inferInstance (Category.id_comp _).symm c hc
          (pullback.fst c.pt.hom (g i)) (pullback.snd c.pt.hom (g i))
          (IsPullback.of_hasPullback _ _)
      · have := hg i
        have := hg j
        exact (hloc i).1 (pullback (g i) (g j)) (pullback.fst (g i) (g j))
          (pullback.fst (g i) (g j) ≫ g i) inferInstance rfl c hc _ _
          (isPullback_overlap c.pt.hom (g i) (g j)) }

end Stacks.FundamentalGroup

end
