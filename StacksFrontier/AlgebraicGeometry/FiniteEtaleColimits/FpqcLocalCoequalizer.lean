module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.CoequalizerBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.LocalCoequalizer
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.SplitCoverRefinement
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# The fpqc-local description of the coequalizers of finite étale covers

Let `X` be a scheme. For a coequalizer `Y ⇉ Z ⟶ T` in the category `FÉt_X` of schemes finite
étale over `X`, the underlying cofork of schemes becomes a coequalizer after base change to each
member, and to each pairwise overlap, of an fpqc covering of `T`. The covering is the base change
to `T` of an étale covering of `X` over whose members both covers split and both morphisms become
morphisms induced by maps of index types.

## Main definitions

* `Stacks.FundamentalGroup.fEtTop` — the terminal finite étale cover `𝟙 X`.
* `Stacks.FundamentalGroup.splitCoverInj` — the inclusion of the `i`-th copy of the base into the
  split cover, exhibiting `∐_{i : ι} X` as the coproduct of `ι` copies of `fEtTop X`.
* `Stacks.FundamentalGroup.baseChangeSplitCoverIso` — the base change of a finite coproduct of
  copies of the base is the finite coproduct of copies of the new base.
* `Stacks.FundamentalGroup.SplitsIndexwise` — the property of a morphism `g : V ⟶ X` that after
  base change along `g` both covers split and both morphisms are index maps.

## Main results

* `Stacks.FundamentalGroup.map_splitCoverMap_baseChangeSplitCoverIso` — the identification
  `Stacks.FundamentalGroup.baseChangeSplitCoverIso` is compatible with the morphisms induced by
  maps of index types.
* `Stacks.FundamentalGroup.SplitsIndexwise.comp` — splitting indexwise is stable under further
  base change.
* `Stacks.FundamentalGroup.exists_splitsIndexwise` — through every point of `X` there is an étale
  neighbourhood over which the pair splits indexwise.
* `Stacks.FundamentalGroup.nonempty_isColimit_baseChangeCofork_of_splitsIndexwise` — the base
  change of a coequalizer of `FÉt_X` along a morphism over which the pair splits indexwise is a
  coequalizer of schemes.
* `Stacks.FundamentalGroup.exists_fpqcCover_isColimit_baseChangeCofork_finiteEtaleOver` — every
  coequalizer in `FÉt_X` is a coequalizer of the underlying schemes after base change to each
  member and each pairwise overlap of some fpqc covering of its target.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.FundamentalGroup

/-! ### Transporting colimits along isomorphisms -/

section Transport

variable {C : Type*} [Category* C]

/-- **Transport of a coequalizer along isomorphisms of the parallel pair and of the apex.** -/
def isColimitCoforkOfIso {Y Z Y' Z' W : C} {a b : Y ⟶ Z} {a' b' : Y' ⟶ Z'}
    (u : Y ≅ Y') (v : Z ≅ Z') (ha : a ≫ v.hom = u.hom ≫ a') (hb : b ≫ v.hom = u.hom ≫ b')
    (c' : Cofork a' b') (hc' : IsColimit c') (w : c'.pt ≅ W) (π : Z ⟶ W)
    (hπ : v.hom ≫ c'.π ≫ w.hom = π) (hab : a ≫ π = b ≫ π) :
    IsColimit (Cofork.ofπ π hab) := by
  subst hπ
  have h1 : a' ≫ v.inv = u.inv ≫ a := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : b' ≫ v.inv = u.inv ≫ b := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hcond : ∀ s : Cofork a b, a' ≫ v.inv ≫ s.π = b' ≫ v.inv ≫ s.π := fun s ↦ by
    rw [← Category.assoc, h1, ← Category.assoc, h2, Category.assoc, Category.assoc, s.condition]
  refine Cofork.IsColimit.mk _
    (fun s ↦ w.inv ≫ hc'.desc (Cofork.ofπ (v.inv ≫ s.π) (hcond s))) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · have hd := hc'.fac (Cofork.ofπ (v.inv ≫ s.π) (hcond s)) WalkingParallelPair.one
    simp only [Cofork.π_ofπ, Category.assoc, Iso.hom_inv_id_assoc] at hd ⊢
    rw [show c'.ι.app WalkingParallelPair.one = Cofork.π c' from rfl] at hd
    rw [hd]
    simp
  · rw [Cofork.π_ofπ] at hm
    rw [Iso.eq_inv_comp]
    refine hc'.uniq (Cofork.ofπ (v.inv ≫ s.π) (hcond s)) _ fun j ↦ ?_
    have key : Cofork.π c' ≫ w.hom ≫ m = v.inv ≫ s.π := by
      rw [Iso.eq_inv_comp]
      simp only [Category.assoc] at hm ⊢
      exact hm
    cases j
    · rw [Cofork.app_zero_eq_comp_π_left, Cofork.app_zero_eq_comp_π_left, Category.assoc,
        Cofork.π_ofπ]
      exact congrArg (fun z ↦ a' ≫ z) key
    · exact key

/-- **Reindexing a colimit cofan along isomorphisms of the family.** -/
def isColimitCofanOfIso {β : Type*} {A B : β → C} (P : C)
    (p : ∀ i, A i ⟶ P) (hp : IsColimit (Cofan.mk P p)) (θ : ∀ i, B i ≅ A i) :
    IsColimit (Cofan.mk P (fun i ↦ (θ i).hom ≫ p i)) := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ hp.desc (Cofan.mk t.pt (fun i ↦ (θ i).inv ≫ t.inj i))) (fun t j ↦ ?_)
    (fun t m hm ↦ hp.hom_ext fun j ↦ ?_)
  · have h := hp.fac (Cofan.mk t.pt (fun i ↦ (θ i).inv ≫ t.inj i)) ⟨j⟩
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, cofan_mk_inj, Category.assoc] at h ⊢
    rw [h, Iso.hom_inv_id_assoc]
  · have h1 := hp.fac (Cofan.mk t.pt (fun i ↦ (θ i).inv ≫ t.inj i)) j
    have h2 := hm j.as
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, cofan_mk_inj, Category.assoc] at h1 h2 ⊢
    rw [h1, ← h2, Iso.inv_hom_id_assoc]

end Transport

/-! ### The split cover as a coproduct of copies of the terminal cover -/

variable {X X' : Scheme.{u}}

/-- The terminal finite étale cover of `X`, namely the identity of `X`. -/
@[reducible] def fEtTop (X : Scheme.{u}) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ _)

variable (X) in
/-- The inclusion of the `i`-th copy of the base into the split cover `∐_{i : ι} X`. -/
def splitCoverInj (ι : Type u) [Finite ι] (i : ι) : fEtTop X ⟶ splitCover X ι :=
  MorphismProperty.Over.homMk (Sigma.ι (fun _ : ι ↦ X) i) (Sigma.ι_comp_desc _ _)

variable (X) in
/-- The constant diagram at the terminal finite étale cover. -/
def splitDiag (ι : Type u) : Discrete ι ⥤ FiniteEtaleOver X :=
  Discrete.functor (fun _ : ι ↦ fEtTop X)

variable (X) in
/-- **The split cover is the coproduct of `ι` copies of the terminal cover.** -/
def isColimitCofanSplitCover (ι : Type u) [Finite ι] :
    IsColimit (Cofan.mk (splitCover X ι) (splitCoverInj X ι)) :=
  isColimitSigmaCocone X (splitDiag X ι)

/-- The morphism induced by a map of index types sends the `j`-th inclusion to the `ρ j`-th
one. -/
lemma splitCoverInj_comp_splitCoverMap {ι κ : Type u} [Finite ι] [Finite κ] (ρ : κ → ι) (j : κ) :
    splitCoverInj X κ j ≫ splitCoverMap X ρ = splitCoverInj X ι (ρ j) :=
  MorphismProperty.Over.Hom.ext (ι_sigmaIndexMap X ρ j)

/-! ### Base change of the split covers -/

/-- Base change sends the terminal cover to the terminal cover. -/
def baseChangeTopIso (g : X' ⟶ X) : (finiteEtaleBaseChange g).obj (fEtTop X) ≅ fEtTop X' :=
  have := preservesFiniteLimits_finiteEtaleBaseChange g
  (IsTerminal.isTerminalObj (finiteEtaleBaseChange g) _
      (MorphismProperty.Over.mkIdTerminal _ _)).uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal _ _)

/-- On underlying schemes, the inverse of `Stacks.FundamentalGroup.baseChangeTopIso` followed by
the projection to the original cover is the morphism one is base changing along. -/
lemma baseChangeTopIso_inv_left_proj (g : X' ⟶ X) :
    (baseChangeTopIso g).inv.left ≫ finiteEtaleBaseChangeProj g (fEtTop X) = g :=
  have h1 : (baseChangeTopIso g).inv.left ≫
      finiteEtaleBaseChangeProj g (fEtTop X) ≫ (fEtTop X).hom = (fEtTop X').hom ≫ g := by
    rw [finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc, MorphismProperty.Over.w]
  (congrArg (fun z ↦ (baseChangeTopIso g).inv.left ≫ z)
      (Category.comp_id (finiteEtaleBaseChangeProj g (fEtTop X))).symm).trans
    (h1.trans (Category.id_comp g))

/-- **Base change sends the split cover to the split cover**: the base change of a finite
coproduct of copies of the base along one leg is the finite coproduct of copies of the new
base. -/
def baseChangeSplitCoverIso (g : X' ⟶ X) (ι : Type u) [Finite ι] :
    (finiteEtaleBaseChange g).obj (splitCover X ι) ≅ splitCover X' ι :=
  have := preservesFiniteCoproducts_finiteEtaleBaseChange g
  IsColimit.coconePointUniqueUpToIso
    (isColimitCofanOfIso _ _
      (isColimitCofanMkObjOfIsColimit (finiteEtaleBaseChange g) (fun _ : ι ↦ fEtTop X)
        (splitCoverInj X ι) (isColimitCofanSplitCover X ι))
      (fun _ ↦ (baseChangeTopIso g).symm))
    (isColimitCofanSplitCover X' ι)

/-- The identification of the base change of a split cover with a split cover is the one that
matches up the inclusions of the summands. -/
lemma splitCoverInj_baseChangeSplitCoverIso (g : X' ⟶ X) {ι : Type u} [Finite ι] (i : ι) :
    (baseChangeTopIso g).inv ≫ (finiteEtaleBaseChange g).map (splitCoverInj X ι i) ≫
        (baseChangeSplitCoverIso g ι).hom = splitCoverInj X' ι i := by
  have := preservesFiniteCoproducts_finiteEtaleBaseChange g
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitCofanOfIso _ _
      (isColimitCofanMkObjOfIsColimit (finiteEtaleBaseChange g) (fun _ : ι ↦ fEtTop X)
        (splitCoverInj X ι) (isColimitCofanSplitCover X ι))
      (fun _ ↦ (baseChangeTopIso g).symm))
    (isColimitCofanSplitCover X' ι) (⟨i⟩ : Discrete ι)
  exact (Category.assoc _ _ _).symm.trans h

/-- The inverse of the identification of a base-changed split cover sends the `i`-th inclusion to
the base change of the `i`-th inclusion. -/
private lemma splitCoverInj_comp_baseChangeSplitCoverIso_inv (g : X' ⟶ X) {ι : Type u} [Finite ι]
    (i : ι) : splitCoverInj X' ι i ≫ (baseChangeSplitCoverIso g ι).inv =
      (baseChangeTopIso g).inv ≫ (finiteEtaleBaseChange g).map (splitCoverInj X ι i) := by
  rw [← splitCoverInj_baseChangeSplitCoverIso g (ι := ι) i]
  simp

/-- The identification of the base changes of the split covers is compatible with the morphisms
induced by a map of index types. -/
lemma map_splitCoverMap_baseChangeSplitCoverIso (g : X' ⟶ X) {ι κ : Type u} [Finite ι] [Finite κ]
    (ρ : κ → ι) :
    (finiteEtaleBaseChange g).map (splitCoverMap X ρ) ≫ (baseChangeSplitCoverIso g ι).hom =
      (baseChangeSplitCoverIso g κ).hom ≫ splitCoverMap X' ρ := by
  have := preservesFiniteCoproducts_finiteEtaleBaseChange g
  refine (isColimitCofanOfIso _ _
    (isColimitCofanMkObjOfIsColimit (finiteEtaleBaseChange g) (fun _ : κ ↦ fEtTop X)
      (splitCoverInj X κ) (isColimitCofanSplitCover X κ))
    (fun _ ↦ (baseChangeTopIso g).symm)).hom_ext fun j ↦ ?_
  have hι := splitCoverInj_baseChangeSplitCoverIso g (ι := ι) (ρ j.as)
  have hκ : ((baseChangeTopIso g).inv ≫
      (finiteEtaleBaseChange g).map (splitCoverInj X κ j.as) ≫
        (baseChangeSplitCoverIso g κ).hom) ≫ splitCoverMap X' ρ =
      splitCoverInj X' κ j.as ≫ splitCoverMap X' ρ := by
    rw [splitCoverInj_baseChangeSplitCoverIso]
  simp only [Category.assoc] at hκ
  simp only [Cofan.mk_pt, Cofan.mk_ι_app, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, splitCoverInj_comp_splitCoverMap, hι, hκ,
    splitCoverInj_comp_splitCoverMap]

/-! ### Morphisms into a base-changed split cover -/

/-- The morphism `∐_{i : ι} X' ⟶ ∐_{i : ι} X` induced by `g : X' ⟶ X`, read off the
identification of the base change of the split cover. -/
def splitCoverBaseChangeProj (g : X' ⟶ X) (ι : Type u) [Finite ι] :
    (splitCover X' ι).left ⟶ (splitCover X ι).left :=
  (baseChangeSplitCoverIso g ι).inv.left ≫ finiteEtaleBaseChangeProj g (splitCover X ι)

/-- On the `i`-th summand, `Stacks.FundamentalGroup.splitCoverBaseChangeProj` is the projection
to the original base followed by the `i`-th inclusion. -/
lemma splitCoverInj_left_splitCoverBaseChangeProj (g : X' ⟶ X) {ι : Type u} [Finite ι] (i : ι) :
    (splitCoverInj X' ι i).left ≫ splitCoverBaseChangeProj g ι =
      (baseChangeTopIso g).inv.left ≫ finiteEtaleBaseChangeProj g (fEtTop X) ≫
        (splitCoverInj X ι i).left := by
  have h'' := congrArg (fun k ↦ k.left ≫ finiteEtaleBaseChangeProj g (splitCover X ι))
    (splitCoverInj_comp_baseChangeSplitCoverIso_inv g i)
  simp only [MorphismProperty.Comma.comp_left, Category.assoc] at h''
  rw [splitCoverBaseChangeProj, h'', finiteEtaleBaseChangeProj_naturality]

/-- **Morphisms of finite étale covers into a split cover are determined by their composite with
`Stacks.FundamentalGroup.splitCoverBaseChangeProj`.** -/
lemma hom_ext_splitCoverBaseChangeProj (g : X' ⟶ X) {ι : Type u} [Finite ι]
    {P : FiniteEtaleOver X'} {m₁ m₂ : P ⟶ splitCover X' ι}
    (h : m₁.left ≫ splitCoverBaseChangeProj g ι = m₂.left ≫ splitCoverBaseChangeProj g ι) :
    m₁ = m₂ := by
  have key : m₁ ≫ (baseChangeSplitCoverIso g ι).inv = m₂ ≫ (baseChangeSplitCoverIso g ι).inv := by
    refine finiteEtaleOver_hom_ext g ?_
    simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    simpa only [splitCoverBaseChangeProj, Category.assoc] using h
  simpa using congrArg (fun k ↦ k ≫ (baseChangeSplitCoverIso g ι).hom) key

/-! ### Sections of a split cover that land in one summand -/

/-- A section of the fold map of a split cover which lands in the image of one summand over an
open of the base is that summand's inclusion over the open. -/
lemma comp_eq_comp_sigmaι_of_le {U : Scheme.{u}} {ι : Type u} (i₀ : ι)
    (t : U ⟶ ∐ fun _ : ι ↦ U) (ht : t ≫ (Sigma.desc fun _ : ι ↦ 𝟙 U) = 𝟙 U)
    (W : U.Opens) (hW : W ≤ t ⁻¹ᵁ (Sigma.ι (fun _ : ι ↦ U) i₀).opensRange) :
    W.ι ≫ t = W.ι ≫ Sigma.ι (fun _ : ι ↦ U) i₀ := by
  have hrange : Set.range (W.ι ≫ t) ⊆ Set.range (Sigma.ι (fun _ : ι ↦ U) i₀) := by
    rintro y ⟨w, rfl⟩
    have hw := hW w.2
    rw [Scheme.Hom.mem_preimage] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, by rw [hz]; rfl⟩
  have hfac := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : ι ↦ U) i₀) (W.ι ≫ t) hrange
  have hr : IsOpenImmersion.lift (Sigma.ι (fun _ : ι ↦ U) i₀) (W.ι ≫ t) hrange = W.ι := by
    have h2 := congrArg (fun l ↦ l ≫ (Sigma.desc fun _ : ι ↦ 𝟙 U)) hfac
    simp only [Category.assoc, Sigma.ι_comp_desc, Category.comp_id, ht] at h2
    simpa using h2
  rw [← hfac, hr]

/-- **A morphism from the terminal cover to a split cover which agrees with the inclusion of one
summand after composing with `k` becomes that summand's inclusion after base change along `k`.**
-/
lemma map_eq_splitCoverInj_of_comp_eq {U W : Scheme.{u}} (k : W ⟶ U) {ι : Type u} [Finite ι]
    (i₀ : ι) (t : fEtTop U ⟶ splitCover U ι)
    (h : k ≫ t.left = k ≫ (splitCoverInj U ι i₀).left) :
    (baseChangeTopIso k).inv ≫ (finiteEtaleBaseChange k).map t ≫
      (baseChangeSplitCoverIso k ι).hom = splitCoverInj W ι i₀ := by
  refine hom_ext_splitCoverBaseChangeProj k ?_
  have hiso : ∀ {T : Scheme.{u}}
      (z : ((finiteEtaleBaseChange k).obj (splitCover U ι)).left ⟶ T),
      (baseChangeSplitCoverIso k ι).hom.left ≫
        (baseChangeSplitCoverIso k ι).inv.left ≫ z = z := fun z ↦ by
    rw [← Category.assoc, ← MorphismProperty.Comma.comp_left, Iso.hom_inv_id]
    exact Category.id_comp z
  have hL : ((baseChangeTopIso k).inv ≫ (finiteEtaleBaseChange k).map t ≫
        (baseChangeSplitCoverIso k ι).hom).left ≫ splitCoverBaseChangeProj k ι =
      (baseChangeTopIso k).inv.left ≫ finiteEtaleBaseChangeProj k (fEtTop U) ≫ t.left := by
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
      splitCoverBaseChangeProj]
    simp only [Category.assoc]
    rw [hiso, finiteEtaleBaseChangeProj_naturality]
  rw [hL, splitCoverInj_left_splitCoverBaseChangeProj]
  have he := baseChangeTopIso_inv_left_proj k
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ t.left) he).trans (h.trans
      (congrArg (fun z ↦ z ≫ (splitCoverInj U ι i₀).left) he).symm))).trans
    (Category.assoc _ _ _)

/-! ### Base change of a trivialisation -/

section Trivialisation

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X}

/-- **Base change of a trivialised square.** If after base change along `g` the morphism `a`
becomes `A` under identifications of the base changes of `Y` and `Z` with split covers, then
after base change along `k ≫ g` it becomes the base change of `A`. -/
lemma map_comp_baseChangeTrivialisation (a : Y ⟶ Z) {V V' : Scheme.{u}} (g : V ⟶ X) (k : V' ⟶ V)
    {ι κ : Type u} [Finite ι] [Finite κ]
    (u : (finiteEtaleBaseChange g).obj Y ≅ splitCover V κ)
    (v : (finiteEtaleBaseChange g).obj Z ≅ splitCover V ι)
    (A : splitCover V κ ⟶ splitCover V ι)
    (hA : (finiteEtaleBaseChange g).map a ≫ v.hom = u.hom ≫ A) :
    (finiteEtaleBaseChange (k ≫ g)).map a ≫
        ((finiteEtaleBaseChangeComp k g).app Z ≪≫
          (finiteEtaleBaseChange k).mapIso v ≪≫ baseChangeSplitCoverIso k ι).hom =
      ((finiteEtaleBaseChangeComp k g).app Y ≪≫
          (finiteEtaleBaseChange k).mapIso u ≪≫ baseChangeSplitCoverIso k κ).hom ≫
        ((baseChangeSplitCoverIso k κ).inv ≫ (finiteEtaleBaseChange k).map A ≫
          (baseChangeSplitCoverIso k ι).hom) := by
  have hnat := (finiteEtaleBaseChangeComp k g).hom.naturality a
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hnat]
  simp only [Functor.comp_map, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, hA, Functor.map_comp]
  simp

/-- The pair `a, b` becomes a pair of index maps of split covers after base change along `g`. -/
def SplitsIndexwise (a b : Y ⟶ Z) {V : Scheme.{u}} (g : V ⟶ X) : Prop :=
  ∃ (ι κ : Type u) (_ : Finite ι) (_ : Finite κ) (σ τ : κ → ι)
    (u : (finiteEtaleBaseChange g).obj Y ≅ splitCover V κ)
    (v : (finiteEtaleBaseChange g).obj Z ≅ splitCover V ι),
    (finiteEtaleBaseChange g).map a ≫ v.hom = u.hom ≫ splitCoverMap V σ ∧
    (finiteEtaleBaseChange g).map b ≫ v.hom = u.hom ≫ splitCoverMap V τ

/-- **Being split indexwise is stable under further base change.** -/
lemma SplitsIndexwise.comp {a b : Y ⟶ Z} {V V' : Scheme.{u}} {g : V ⟶ X}
    (h : SplitsIndexwise a b g) (k : V' ⟶ V) : SplitsIndexwise a b (k ≫ g) := by
  obtain ⟨ι, κ, hι, hκ, σ, τ, u, v, hσ, hτ⟩ := h
  have hcancel : ∀ ρ : κ → ι, (baseChangeSplitCoverIso k κ).inv ≫
      (finiteEtaleBaseChange k).map (splitCoverMap V ρ) ≫ (baseChangeSplitCoverIso k ι).hom =
      splitCoverMap V' ρ := fun ρ ↦ by
    rw [Iso.inv_comp_eq]
    exact map_splitCoverMap_baseChangeSplitCoverIso k ρ
  refine ⟨ι, κ, hι, hκ, σ, τ,
    (finiteEtaleBaseChangeComp k g).app Y ≪≫
      (finiteEtaleBaseChange k).mapIso u ≪≫ baseChangeSplitCoverIso k κ,
    (finiteEtaleBaseChangeComp k g).app Z ≪≫
      (finiteEtaleBaseChange k).mapIso v ≪≫ baseChangeSplitCoverIso k ι, ?_, ?_⟩
  · rw [map_comp_baseChangeTrivialisation a g k u v _ hσ, hcancel]
  · rw [map_comp_baseChangeTrivialisation b g k u v _ hτ, hcancel]

end Trivialisation

/-! ### The trivialising étale covering -/

section Exists

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X}

/-- Through every point of the base there is an étale neighbourhood over which both covers become
split *and* both morphisms become the morphisms induced by maps of index types. -/
lemma exists_splitsIndexwise (a b : Y ⟶ Z) (x : X) :
    ∃ (V : Scheme.{u}) (g : V ⟶ X) (_ : Etale g) (y : V), g y = x ∧ SplitsIndexwise a b g := by
  have hZf : IsFinite Z.hom := Z.prop.1
  have hZe : Etale Z.hom := Z.prop.2
  obtain ⟨U₁, g₁, hg₁, y₁, hy₁, ι, hι, e₁, he₁⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_sigma Z.hom x
  have := hg₁
  let v₀ : (finiteEtaleBaseChange g₁).obj Z ≅ splitCover U₁ ι :=
    MorphismProperty.Over.isoMk e₁ he₁
  have hYf : IsFinite ((finiteEtaleBaseChange g₁).obj Y).hom :=
    ((finiteEtaleBaseChange g₁).obj Y).prop.1
  have hYe : Etale ((finiteEtaleBaseChange g₁).obj Y).hom :=
    ((finiteEtaleBaseChange g₁).obj Y).prop.2
  obtain ⟨U₂, g₂, hg₂, y₂, hy₂, κ, hκ, e₂, he₂⟩ :=
    Stacks.Etale.exists_etale_pullback_iso_sigma
      ((finiteEtaleBaseChange g₁).obj Y).hom y₁
  have := hg₂
  let uu : (finiteEtaleBaseChange (g₂ ≫ g₁)).obj Y ≅ splitCover U₂ κ :=
    (finiteEtaleBaseChangeComp g₂ g₁).app Y ≪≫ MorphismProperty.Over.isoMk e₂ he₂
  let vv : (finiteEtaleBaseChange (g₂ ≫ g₁)).obj Z ≅ splitCover U₂ ι :=
    (finiteEtaleBaseChangeComp g₂ g₁).app Z ≪≫
      (finiteEtaleBaseChange g₂).mapIso v₀ ≪≫ baseChangeSplitCoverIso g₂ ι
  have hfac : ∀ f : Y ⟶ Z, ∃ C, (finiteEtaleBaseChange (g₂ ≫ g₁)).map f ≫ vv.hom = uu.hom ≫ C :=
    fun f ↦ ⟨uu.inv ≫ (finiteEtaleBaseChange (g₂ ≫ g₁)).map f ≫ vv.hom, by simp⟩
  obtain ⟨A', hA⟩ := hfac a
  obtain ⟨B', hB⟩ := hfac b
  obtain ⟨Vop, hsup, hle⟩ := exists_openCover_le_preimage_opensRange
    (X := U₂) (ι := ι) (κ := κ ⊕ κ)
    (fun j ↦ Sum.elim (fun j' ↦ (splitCoverInj U₂ κ j' ≫ A').left)
      (fun j' ↦ (splitCoverInj U₂ κ j' ≫ B').left) j)
  have hmem : y₂ ∈ (⨆ φ, Vop φ) := by rw [hsup]; trivial
  rw [Opens.mem_iSup] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨(Vop φ).toScheme, (Vop φ).ι ≫ g₂ ≫ g₁, inferInstance, ⟨y₂, hφ⟩, ?_, ?_⟩
  · have h1 : ((Vop φ).ι ≫ g₂ ≫ g₁) ⟨y₂, hφ⟩ = g₁ (g₂ y₂) := rfl
    have h2 : g₁ (g₂ y₂) = x := by rw [hy₂]; exact hy₁
    exact h1.trans h2
  · have key : ∀ (C : splitCover U₂ κ ⟶ splitCover U₂ ι) (ρ : κ → ι),
        (∀ j, Vop φ ≤ (splitCoverInj U₂ κ j ≫ C).left ⁻¹ᵁ
          (Sigma.ι (fun _ : ι ↦ U₂) (ρ j)).opensRange) →
        (baseChangeSplitCoverIso (Vop φ).ι κ).inv ≫
            (finiteEtaleBaseChange (Vop φ).ι).map C ≫
              (baseChangeSplitCoverIso (Vop φ).ι ι).hom = splitCoverMap (Vop φ).toScheme ρ := by
      intro C ρ hle'
      refine (isColimitCofanSplitCover (Vop φ).toScheme κ).hom_ext fun j ↦ ?_
      simp only [Cofan.mk_pt, Cofan.mk_ι_app]
      rw [← Category.assoc, splitCoverInj_comp_baseChangeSplitCoverIso_inv,
        splitCoverInj_comp_splitCoverMap]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc]
      exact map_eq_splitCoverInj_of_comp_eq (Vop φ).ι (ρ j.as) _
        (comp_eq_comp_sigmaι_of_le (ρ j.as) _
          (MorphismProperty.Over.w (splitCoverInj U₂ κ j.as ≫ C)) (Vop φ) (hle' j.as))
    refine ⟨ι, κ, hι, hκ, fun j ↦ φ (Sum.inl j), fun j ↦ φ (Sum.inr j),
      (finiteEtaleBaseChangeComp (Vop φ).ι (g₂ ≫ g₁)).app Y ≪≫
        (finiteEtaleBaseChange (Vop φ).ι).mapIso uu ≪≫
          baseChangeSplitCoverIso (Vop φ).ι κ,
      (finiteEtaleBaseChangeComp (Vop φ).ι (g₂ ≫ g₁)).app Z ≪≫
        (finiteEtaleBaseChange (Vop φ).ι).mapIso vv ≪≫
          baseChangeSplitCoverIso (Vop φ).ι ι, ?_, ?_⟩
    · rw [map_comp_baseChangeTrivialisation a (g₂ ≫ g₁) (Vop φ).ι uu vv A' hA]
      rw [key A' (fun j ↦ φ (Sum.inl j)) fun j ↦ hle φ (Sum.inl j)]
    · rw [map_comp_baseChangeTrivialisation b (g₂ ≫ g₁) (Vop φ).ι uu vv B' hB]
      rw [key B' (fun j ↦ φ (Sum.inr j)) fun j ↦ hle φ (Sum.inr j)]

end Exists

/-! ### The base-changed cofork over a trivialising morphism -/

/-- The underlying isomorphism of schemes of an isomorphism of finite étale covers. -/
def leftIso {V : Scheme.{u}} {A B : FiniteEtaleOver V} (e : A ≅ B) : A.left ≅ B.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by rw [← MorphismProperty.Comma.comp_left, e.hom_inv_id]; rfl
  inv_hom_id := by rw [← MorphismProperty.Comma.comp_left, e.inv_hom_id]; rfl

/-- The forward morphism of `Stacks.FundamentalGroup.leftIso`. -/
@[simp] lemma leftIso_hom {V : Scheme.{u}} {A B : FiniteEtaleOver V} (e : A ≅ B) :
    (leftIso e).hom = e.hom.left := rfl

/-- The inverse morphism of `Stacks.FundamentalGroup.leftIso`. -/
@[simp] lemma leftIso_inv {V : Scheme.{u}} {A B : FiniteEtaleOver V} (e : A ≅ B) :
    (leftIso e).inv = e.inv.left := rfl

section BaseChangeCofork

/-- The first projection of a base-changed morphism `AlgebraicGeometry.baseChangeHom`. -/
private lemma baseChangeHom_comp_fst {A B C D : Scheme.{u}} (α : A ⟶ B) (d : A ⟶ C)
    (γ : B ⟶ C) (sm : D ⟶ C) (hα : α ≫ γ = d) :
    baseChangeHom α d γ sm hα ≫ pullback.fst γ sm = pullback.fst d sm ≫ α :=
  pullback.lift_fst _ _ _

/-- The second projection of a base-changed morphism `AlgebraicGeometry.baseChangeHom`. -/
private lemma baseChangeHom_comp_snd {A B C D : Scheme.{u}} (α : A ⟶ B) (d : A ⟶ C)
    (γ : B ⟶ C) (sm : D ⟶ C) (hα : α ≫ γ = d) :
    baseChangeHom α d γ sm hα ≫ pullback.snd γ sm = pullback.snd d sm :=
  pullback.lift_snd _ _ _

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X} {a b : Y ⟶ Z}

/-- **The base change of a coequalizer of finite étale covers to a trivialising morphism is a
coequalizer of schemes.** -/
lemma nonempty_isColimit_baseChangeCofork_of_splitsIndexwise (c : Cofork a b) (hc : IsColimit c)
    {V : Scheme.{u}} {g : V ⟶ X} (hg : SplitsIndexwise a b g)
    {S : Scheme.{u}} (s : S ⟶ c.pt.left) (t : S ⟶ V) (hS : IsPullback s t c.pt.hom g) :
    Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
      (congrArg (fun k ↦ k.left) c.condition) s)) := by
  obtain ⟨ι, κ, hι, hκ, σ, τ, u, v, hσ, hτ⟩ := hg
  have hc0 : IsColimit (Cofork.ofπ c.π c.condition) :=
    IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  have hcF : IsColimit (Cofork.ofπ ((finiteEtaleBaseChange g).map c.π)
      (by simp only [← Functor.map_comp, c.condition]) :
      Cofork ((finiteEtaleBaseChange g).map a) ((finiteEtaleBaseChange g).map b)) :=
    isColimitCoforkMapOfIsColimit (finiteEtaleBaseChange g) c.condition hc0
  have hab1 : (finiteEtaleBaseChange g).map a ≫ v.hom ≫ (splitCoverCofork V σ τ).π =
      (finiteEtaleBaseChange g).map b ≫ v.hom ≫ (splitCoverCofork V σ τ).π := by
    rw [← Category.assoc, hσ, ← Category.assoc, hτ, Category.assoc, Category.assoc]
    exact congrArg (fun z ↦ u.hom ≫ z) (splitCoverCofork V σ τ).condition
  have hC₁ : IsColimit (Cofork.ofπ (v.hom ≫ (splitCoverCofork V σ τ).π) hab1) :=
    isColimitCoforkOfIso u v hσ hτ (splitCoverCofork V σ τ)
      (isColimit_splitCoverCofork V σ τ) (Iso.refl _) _ (by simp) hab1
  set θ := IsColimit.coconePointUniqueUpToIso hC₁ hcF with hθdef
  have hθ : (v.hom ≫ (splitCoverCofork V σ τ).π) ≫ θ.hom =
      (finiteEtaleBaseChange g).map c.π :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hC₁ hcF WalkingParallelPair.one
  have hwπ : c.π.left ≫ c.pt.hom = Z.hom := MorphismProperty.Over.w c.π
  have hwaπ : (a.left ≫ c.π.left) ≫ c.pt.hom = Y.hom := by
    rw [Category.assoc, hwπ]; exact MorphismProperty.Over.w a
  have hiso : ∀ (P : FiniteEtaleOver X) (p : P.left ⟶ c.pt.left), p ≫ c.pt.hom = P.hom →
      ∃ e : pullback p s ≅ ((finiteEtaleBaseChange g).obj P).left,
        e.hom ≫ finiteEtaleBaseChangeProj g P = pullback.fst p s ∧
        e.hom ≫ ((finiteEtaleBaseChange g).obj P).hom = pullback.snd p s ≫ t :=
    fun P p hp ↦ by
      have hp' : IsPullback (pullback.fst p s) (pullback.snd p s ≫ t) P.hom g := by
        rw [← hp]; exact (IsPullback.of_hasPullback p s).paste_vert hS
      have hbc : IsPullback (finiteEtaleBaseChangeProj g P)
          ((finiteEtaleBaseChange g).obj P).hom P.hom g := IsPullback.of_hasPullback P.hom g
      exact ⟨hp'.isoIsPullback _ _ hbc, IsPullback.isoIsPullback_hom_fst _ _ hp' hbc,
        IsPullback.isoIsPullback_hom_snd _ _ hp' hbc⟩
  have hbcZ : IsPullback (finiteEtaleBaseChangeProj g Z)
      ((finiteEtaleBaseChange g).obj Z).hom Z.hom g := IsPullback.of_hasPullback Z.hom g
  have hbcP : IsPullback (finiteEtaleBaseChangeProj g c.pt)
      ((finiteEtaleBaseChange g).obj c.pt).hom c.pt.hom g :=
    IsPullback.of_hasPullback c.pt.hom g
  obtain ⟨u', hu'fst, hu'snd⟩ := hiso Y _ hwaπ
  obtain ⟨v', hv'fst, hv'snd⟩ := hiso Z _ hwπ
  have hpair : ∀ (φ : Y ⟶ Z) (hφ : φ.left ≫ c.π.left = a.left ≫ c.π.left),
      baseChangeHom φ.left (a.left ≫ c.π.left) c.π.left s hφ ≫ v'.hom =
        u'.hom ≫ ((finiteEtaleBaseChange g).map φ).left := fun φ hφ ↦ by
    refine hbcZ.hom_ext ?_ ?_
    · rw [Category.assoc, hv'fst, baseChangeHom_comp_fst, Category.assoc,
        finiteEtaleBaseChangeProj_naturality, ← Category.assoc, hu'fst]
    · rw [Category.assoc, hv'snd, ← Category.assoc, baseChangeHom_comp_snd, Category.assoc,
        MorphismProperty.Over.w, hu'snd]
  have hside : ∀ (φ : Y ⟶ Z) (hφ : φ.left ≫ c.π.left = a.left ≫ c.π.left) (ρ : κ → ι),
      (finiteEtaleBaseChange g).map φ ≫ v.hom = u.hom ≫ splitCoverMap V ρ →
      baseChangeHom φ.left (a.left ≫ c.π.left) c.π.left s hφ ≫ (v' ≪≫ leftIso v).hom =
        (u' ≪≫ leftIso u).hom ≫ (splitCoverMap V ρ).left := fun φ hφ ρ hρ ↦ by
    have h := congrArg (fun k ↦ k.left) hρ
    simp only [MorphismProperty.Comma.comp_left] at h
    rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, hpair φ hφ, Category.assoc,
      Category.assoc, leftIso_hom, leftIso_hom, h]
  refine ⟨isColimitCoforkOfIso (u' ≪≫ leftIso u) (v' ≪≫ leftIso v) (hside a rfl σ hσ)
    (hside b (congrArg (fun k ↦ k.left) c.condition).symm τ hτ)
    (coforkLeft (splitCoverCofork V σ τ)) (isColimit_coforkLeft_splitCoverCofork V σ τ)
    (leftIso θ ≪≫ hbcP.isoIsPullback _ _ hS) _ ?_ _⟩
  have hθL0 : v.hom.left ≫ (splitCoverCofork V σ τ).π.left ≫ θ.hom.left =
      ((finiteEtaleBaseChange g).map c.π).left := by
    simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using
      congrArg (fun k ↦ k.left) hθ
  have hθL : ∀ {T : Scheme.{u}} (z : ((finiteEtaleBaseChange g).obj c.pt).left ⟶ T),
      v.hom.left ≫ (splitCoverCofork V σ τ).π.left ≫ θ.hom.left ≫ z =
        ((finiteEtaleBaseChange g).map c.π).left ≫ z := fun z ↦ by
    rw [← hθL0]; simp only [Category.assoc]
  have hπL : (coforkLeft (splitCoverCofork V σ τ)).π = (splitCoverCofork V σ τ).π.left := rfl
  refine hS.hom_ext ?_ ?_
  · simp only [Iso.trans_hom, leftIso_hom, Category.assoc, hπL]
    rw [IsPullback.isoIsPullback_hom_fst, hθL, finiteEtaleBaseChangeProj_naturality,
      ← Category.assoc, hv'fst]
    exact pullback.condition
  · have hsnd := IsPullback.isoIsPullback_hom_snd _ _ hbcP hS
    simp only [Iso.trans_hom, leftIso_hom, Category.assoc, hπL]
    refine (congrArg (fun z ↦ v'.hom ≫ v.hom.left ≫ (splitCoverCofork V σ τ).π.left ≫
      θ.hom.left ≫ z) hsnd).trans ?_
    refine (congrArg (fun z ↦ v'.hom ≫ z)
      (hθL ((finiteEtaleBaseChange g).obj c.pt).hom)).trans ?_
    exact (congrArg (fun z ↦ v'.hom ≫ z)
      (MorphismProperty.Over.w ((finiteEtaleBaseChange g).map c.π))).trans hv'snd

end BaseChangeCofork

/-! ### The fpqc-local description of the coequalizers -/

section Instance

variable {X : Scheme.{u}} {Y Z : FiniteEtaleOver X}

/-- **The fpqc-local description of the coequalizers.** Every coequalizer in `FÉt_X` is a
coequalizer of the underlying schemes after base change to each member and each pairwise overlap
of an fpqc covering of its target. -/
theorem exists_fpqcCover_isColimit_baseChangeCofork_finiteEtaleOver (a b : Y ⟶ Z)
    (c : Cofork a b) (hc : IsColimit c) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.fpqcPrecoverage c.pt.left,
      (∀ i, Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
        (congrArg (fun k ↦ k.left) c.condition) (𝒰.f i)))) ∧
      (∀ i j, Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
        (congrArg (fun k ↦ k.left) c.condition)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)))) := by
  choose V g hg y hgy hsplit using fun x : X ↦ exists_splitsIndexwise a b x
  have hprop : ∀ x : X, (@Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) (g x) := fun x ↦ by
    have := hg x; exact ⟨inferInstance, inferInstance⟩
  let 𝒲base := Scheme.Cover.mkOfCovers (X := X) (X : Type u) V g
    (fun x ↦ ⟨x, y x, hgy x⟩) hprop
  let 𝒲 : Scheme.Cover.{u} Scheme.fpqcPrecoverage X :=
    { I₀ := (X : Type u), X := V, f := g,
      mem₀ := Scheme.fppfPrecoverage_le_fpqcPrecoverage _ 𝒲base.mem₀ }
  refine ⟨𝒲.pullback₁ c.pt.hom, fun i ↦ ?_, fun i j ↦ ?_⟩
  · exact nonempty_isColimit_baseChangeCofork_of_splitsIndexwise c hc (hsplit i)
      (pullback.fst c.pt.hom (g i)) (pullback.snd c.pt.hom (g i))
      (IsPullback.of_hasPullback c.pt.hom (g i))
  · exact nonempty_isColimit_baseChangeCofork_of_splitsIndexwise c hc
      ((hsplit i).comp (pullback.fst (g i) (g j))) _ _
      (isPullback_overlap c.pt.hom (g i) (g j))

end Instance

end Stacks.FundamentalGroup

end
