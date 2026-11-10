module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.FlatBaseChange

/-!
# Coequalizers of finite étale covers over a base where the covers split

Let `X` be a scheme, let `a, b : Y ⟶ Z` be two morphisms of finite étale covers of `X` and let
`c` be a coequalizer of `a` and `b` in `FÉt_X`. Over a flat `g : P ⟶ X` for which both covers
become disjoint unions of copies of `P` and both morphisms become induced by maps `σ, τ` of the
index sets, the underlying cofork of schemes of the base change of `c` is a coequalizer. The
cofork of schemes is the canonical base-changed cofork `AlgebraicGeometry.baseChangeCofork` of
Stacks Tag 0BMN, along any model of the base change of the apex.

## Main definitions

* `Stacks.FundamentalGroup.baseChangeLeftIso` — the base change of a scheme over `X` as the fibre
  product with a model of the base change of a scheme it maps to.
* `Stacks.FundamentalGroup.finiteEtaleOverIsoMk` — an isomorphism of finite étale covers from an
  isomorphism of the underlying schemes over the base.
* `Stacks.FundamentalGroup.splitCoverBaseChangeIso` — the base change of a split cover is the
  split cover with the same index set.

## Main results

* `Stacks.Etale.isPullback_sigmaDesc_id` — the fold map of a finite disjoint union of copies of
  the base is stable under base change.
* `Stacks.Etale.isSplitCover_pullback_snd` — a split covering stays split after base change.
* `Stacks.FundamentalGroup.isPullback_baseChange_left` — the base change of a morphism of schemes
  over `X` is a fibre product square.
* `Stacks.FundamentalGroup.isColimitBaseChangeCoforkOfIsColimitCoforkLeft` — the cofork of
  schemes underlying a base-changed cofork of covers is the base-changed cofork of Tag 0BMN.
* `Stacks.FundamentalGroup.splitCoverBaseChangeIso_comp` — base change takes an index-induced
  morphism of split covers to the morphism induced by the same map of index types.
* `Stacks.FundamentalGroup.isColimitBaseChangeCoforkOfSplit` — **the coequalizer of two morphisms
  of finite étale covers is a coequalizer of schemes after a flat base change over which both
  covers split and both morphisms are index-induced.**

## References

* [Stacks Project, Tag 0BMN](https://stacks.math.columbia.edu/tag/0BMN)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Etale

/-! ### Base change of a split covering -/

/-- **The fold map of a finite disjoint union of copies of the base is stable under base
change**: `(∐_ι S) ×_S T` is `∐_ι T`, with the two fold maps. This is the van Kampen property of
finite coproducts of schemes. -/
theorem isPullback_sigmaDesc_id {ι : Type*} [Finite ι] {S T : Scheme.{u}} (g : T ⟶ S)
    [HasCoproduct (fun _ : ι => S)] [HasCoproduct (fun _ : ι => T)] :
    IsPullback (Sigma.desc (fun _ : ι => 𝟙 T))
      (Sigma.desc (fun i => g ≫ Sigma.ι (fun _ : ι => S) i)) g
      (Sigma.desc (fun _ : ι => 𝟙 S)) := by
  have hdesc : ∀ {B : Scheme.{u}} (q : ∀ _ : ι, T ⟶ B),
      Cofan.IsColimit.desc (coproductIsCoproduct (fun _ : ι => T)) q = Sigma.desc q := by
    intro B q
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_comp_desc]
    exact Cofan.IsColimit.fac (coproductIsCoproduct (fun _ : ι => T)) q i
  have key := (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : ι => S))).isPullback_of_isColimit_left
    (fun _ => 𝟙 S) (Sigma.desc (fun _ : ι => 𝟙 S)) g (fun _ : ι => 𝟙 T) (fun _ : ι => g)
    (fun _ => IsPullback.of_id_fst) (coproductIsCoproduct (fun _ : ι => T))
    (fun i => Sigma.ι_comp_desc _ _)
  rwa [hdesc, hdesc] at key

/-- A split covering stays a split covering after base change. -/
theorem isSplitCover_pullback_snd {A S T : Scheme.{u}} {f : A ⟶ S} (hf : IsSplitCover f)
    (g : T ⟶ S) : IsSplitCover (pullback.snd f g) := by
  obtain ⟨ι, hι, e, he⟩ := hf
  rw [← he, isSplitCover_pullback_snd_iso_comp]
  refine ⟨ι, hι, ((isPullback_sigmaDesc_id g).flip.isoPullback).symm, ?_⟩
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact ((isPullback_sigmaDesc_id (ι := ι) g).flip.isoPullback_hom_snd).symm

end Stacks.Etale

namespace Stacks.FundamentalGroup

/-! ### Base change of a morphism over the base is a fibre product square -/

section BaseChangeSquare

variable {X P : Scheme.{u}} (g : P ⟶ X) {V V' : Over X} (k : V ⟶ V')

/-- The base change of `k` along `g` commutes with the second projections to `P`. -/
theorem baseChange_left_comp_snd :
    ((Over.pullback g).map k).left ≫ pullback.snd V'.hom g = pullback.snd V.hom g :=
  Over.w ((Over.pullback g).map k)

variable {S : Scheme.{u}} {s : S ⟶ V'.left} {q : S ⟶ P} (hs : IsPullback s q V'.hom g)

/-- The comparison from the base change of `V` to a model of the base change of `V'`. -/
def baseChangeToSource : pullback V.hom g ⟶ S :=
  hs.lift (pullback.fst V.hom g ≫ k.left) (pullback.snd V.hom g) (by
    rw [Category.assoc, Over.w k]
    exact pullback.condition)

/-- The comparison `baseChangeToSource` followed by `s` is the first projection followed by
`k`. -/
@[reassoc (attr := simp)]
theorem baseChangeToSource_comp_fst :
    baseChangeToSource g k hs ≫ s = pullback.fst V.hom g ≫ k.left :=
  hs.lift_fst _ _ _

/-- The comparison `baseChangeToSource` followed by `q` is the second projection to `P`. -/
@[reassoc (attr := simp)]
theorem baseChangeToSource_comp_snd :
    baseChangeToSource g k hs ≫ q = pullback.snd V.hom g :=
  hs.lift_snd _ _ _

/-- **The base change of a morphism of schemes over `X` is a fibre product square**: the base
change of the source is the fibre product of the source with any model of the base change of the
target. -/
theorem isPullback_baseChange_left :
    IsPullback (pullback.fst V.hom g) (baseChangeToSource g k hs) k.left s := by
  refine IsPullback.of_bot ?_ (baseChangeToSource_comp_fst g k hs).symm hs
  rw [baseChangeToSource_comp_snd g k hs, Over.w k]
  exact IsPullback.of_hasPullback V.hom g

/-- The base change of a scheme over `X` along `g`, as the fibre product with a model of the
base change of a scheme it maps to. -/
def baseChangeLeftIso : pullback V.hom g ≅ pullback k.left s :=
  (isPullback_baseChange_left g k hs).isoPullback

/-- The isomorphism `baseChangeLeftIso` commutes with the first projections to `V`. -/
@[reassoc (attr := simp)]
theorem baseChangeLeftIso_hom_fst :
    (baseChangeLeftIso g k hs).hom ≫ pullback.fst k.left s = pullback.fst V.hom g :=
  (isPullback_baseChange_left g k hs).isoPullback_hom_fst

/-- The isomorphism `baseChangeLeftIso` followed by the second projection is the comparison
`baseChangeToSource`. -/
@[reassoc (attr := simp)]
theorem baseChangeLeftIso_hom_snd :
    (baseChangeLeftIso g k hs).hom ≫ pullback.snd k.left s = baseChangeToSource g k hs :=
  (isPullback_baseChange_left g k hs).isoPullback_hom_snd

/-- For the chosen fibre product, the comparison is the base change of the morphism. -/
theorem baseChangeToSource_of_hasPullback :
    baseChangeToSource g k (IsPullback.of_hasPullback V'.hom g) =
      ((Over.pullback g).map k).left := by
  refine pullback.hom_ext ?_ ?_
  · rw [baseChangeToSource_comp_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [baseChangeToSource_comp_snd, baseChange_left_comp_snd]

/-- **The base change of a morphism of schemes over `X` is a fibre product square**, for the
chosen fibre products. -/
theorem isPullback_baseChange_left' :
    IsPullback (pullback.fst V.hom g) (((Over.pullback g).map k).left) k.left
      (pullback.fst V'.hom g) := by
  rw [← baseChangeToSource_of_hasPullback g k]
  exact isPullback_baseChange_left g k (IsPullback.of_hasPullback _ _)

/-- The identification of the base change of a morphism over `X` with the base-changed morphism
of Tag 0BMN. -/
theorem baseChangeLeftIso_comp_baseChangeHom {V V' V'' : Over X} (m m' : V ⟶ V') (n : V' ⟶ V'')
    {S : Scheme.{u}} {s : S ⟶ V''.left} {q : S ⟶ P} (hs : IsPullback s q V''.hom g)
    (hm : m ≫ n = m' ≫ n) :
    (baseChangeLeftIso g (m ≫ n) hs).hom ≫
        baseChangeHom m'.left ((m ≫ n).left) n.left s
          (congrArg (fun t => Over.Hom.left t) hm).symm =
      ((Over.pullback g).map m').left ≫ (baseChangeLeftIso g n hs).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeHom, pullback.lift_fst, baseChangeLeftIso_hom_fst_assoc,
      Category.assoc, baseChangeLeftIso_hom_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, baseChangeHom, pullback.lift_snd, baseChangeLeftIso_hom_snd,
      Category.assoc, baseChangeLeftIso_hom_snd]
    refine hs.hom_ext ?_ ?_
    · simp only [baseChangeToSource_comp_fst, Category.assoc, Over.pullback_map_left,
        pullback.lift_fst_assoc]
      rw [hm]
      rfl
    · simp only [baseChangeToSource_comp_snd, Category.assoc, baseChange_left_comp_snd]

end BaseChangeSquare

/-! ### The base-changed cofork of Tag 0BMN -/

section Cofork

variable {X P : Scheme.{u}} (g : P ⟶ X) {Y Z : FiniteEtaleOver X} (a b : Y ⟶ Z) (c : Cofork a b)

/-- The cofork of schemes underlying the base change of a cofork of finite étale covers is the
canonical base-changed cofork of Tag 0BMN, along any model of the base change of its apex. -/
def isColimitBaseChangeCoforkOfIsColimitCoforkLeft {S : Scheme.{u}} {s : S ⟶ c.pt.left}
    {q : S ⟶ P} (hs : IsPullback s q c.pt.hom g)
    (h : IsColimit (coforkLeft (Cofork.ofπ ((finiteEtaleBaseChange g).map c.π)
      (comp_map_cofork_π g a b c)))) :
    IsColimit (baseChangeCofork a.left b.left c.π.left
      (congrArg (fun k => k.left) c.condition) s) := by
  refine Cofork.isColimitOfIsos _ h _
    (baseChangeLeftIso g ((finiteEtaleOverForgetOver X).map a ≫
      (finiteEtaleOverForgetOver X).map c.π) hs)
    (baseChangeLeftIso g ((finiteEtaleOverForgetOver X).map c.π) hs) hs.isoPullback.symm
    (baseChangeLeftIso_comp_baseChangeHom g ((finiteEtaleOverForgetOver X).map a)
      ((finiteEtaleOverForgetOver X).map a) ((finiteEtaleOverForgetOver X).map c.π) hs rfl)
    (baseChangeLeftIso_comp_baseChangeHom g ((finiteEtaleOverForgetOver X).map a)
      ((finiteEtaleOverForgetOver X).map b) ((finiteEtaleOverForgetOver X).map c.π) hs
      (congrArg (finiteEtaleOverForgetOver X).map c.condition)) ?_
  have key : ((finiteEtaleBaseChange g).map c.π).left ≫ hs.isoPullback.inv =
      baseChangeToSource g ((finiteEtaleOverForgetOver X).map c.π) hs := by
    refine hs.hom_ext ?_ ?_
    · refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => ((finiteEtaleBaseChange g).map c.π).left ≫ t)
        (IsPullback.isoPullback_inv_fst hs)) ?_
      exact (pullback.lift_fst _ _ _).trans
        (baseChangeToSource_comp_fst g ((finiteEtaleOverForgetOver X).map c.π) hs).symm
    · refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => ((finiteEtaleBaseChange g).map c.π).left ≫ t)
        (IsPullback.isoPullback_inv_snd hs)) ?_
      exact (baseChange_left_comp_snd g ((finiteEtaleOverForgetOver X).map c.π)).trans
        (baseChangeToSource_comp_snd g ((finiteEtaleOverForgetOver X).map c.π) hs).symm
  refine Eq.trans (congrArg (fun t => (baseChangeLeftIso g
    ((finiteEtaleOverForgetOver X).map c.π) hs).inv ≫ t) key) ?_
  refine Eq.trans (congrArg (fun t => (baseChangeLeftIso g
    ((finiteEtaleOverForgetOver X).map c.π) hs).inv ≫ t)
    (baseChangeLeftIso_hom_snd g ((finiteEtaleOverForgetOver X).map c.π) hs).symm) ?_
  exact Iso.inv_hom_id_assoc _ _

end Cofork

/-! ### Base change of split covers -/

section SplitBaseChange

variable {X : Scheme.{u}}

/-- An isomorphism of the underlying schemes over `X` compatible with the structure morphisms is
an isomorphism of finite étale covers. -/
def finiteEtaleOverIsoMk {V W : FiniteEtaleOver X} (e : V.left ≅ W.left)
    (he : e.hom ≫ W.hom = V.hom) : V ≅ W where
  hom := MorphismProperty.Over.homMk e.hom he
  inv := MorphismProperty.Over.homMk e.inv (by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp])
  hom_inv_id := MorphismProperty.Over.Hom.ext e.hom_inv_id
  inv_hom_id := MorphismProperty.Over.Hom.ext e.inv_hom_id

variable {P V : Scheme.{u}} (h : V ⟶ P) (ι : Type u) [Finite ι]

/-- The structure morphism of the split cover, as it is spelled after forgetting. -/
theorem forget_splitCover_hom :
    ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom = Sigma.desc (fun _ : ι => 𝟙 P) :=
  rfl

/-- The base change of the split cover `∐_ι P` along `h : V ⟶ P` is the split cover `∐_ι V`. -/
def splitCoverPullbackIso :
    pullback ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h ≅ ∐ (fun _ : ι => V) :=
  ((Stacks.Etale.isPullback_sigmaDesc_id (ι := ι) h).flip.isoPullback).symm

/-- The inverse of `splitCoverPullbackIso` followed by the first projection is the map
`∐_ι V ⟶ ∐_ι P` induced by `h` on each summand. -/
@[reassoc (attr := simp)]
theorem splitCoverPullbackIso_inv_fst :
    (splitCoverPullbackIso h ι).inv ≫
        pullback.fst ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h =
      Sigma.desc (fun i => h ≫ Sigma.ι (fun _ : ι => P) i) :=
  (Stacks.Etale.isPullback_sigmaDesc_id (ι := ι) h).flip.isoPullback_hom_fst

/-- The inverse of `splitCoverPullbackIso` followed by the second projection is the fold map
`∐_ι V ⟶ V`. -/
@[reassoc (attr := simp)]
theorem splitCoverPullbackIso_inv_snd :
    (splitCoverPullbackIso h ι).inv ≫
        pullback.snd ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h =
      Sigma.desc (fun _ : ι => 𝟙 V) :=
  (Stacks.Etale.isPullback_sigmaDesc_id (ι := ι) h).flip.isoPullback_hom_snd

/-- `splitCoverPullbackIso` followed by the fold map `∐_ι V ⟶ V` is the second projection. -/
theorem splitCoverPullbackIso_hom_comp :
    (splitCoverPullbackIso h ι).hom ≫ Sigma.desc (fun _ : ι => 𝟙 V) =
      pullback.snd ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h := by
  rw [← splitCoverPullbackIso_inv_snd h ι, Iso.hom_inv_id_assoc]

/-- The base change of a split finite étale cover along any morphism is the split cover with the
same index set. -/
def splitCoverBaseChangeIso :
    (finiteEtaleBaseChange h).obj (splitCover P ι) ≅ splitCover V ι :=
  finiteEtaleOverIsoMk (splitCoverPullbackIso h ι) (splitCoverPullbackIso_hom_comp h ι)

/-- Base change takes the morphism of split covers induced by a map of index types to the
morphism induced by the same map. -/
theorem splitCoverBaseChangeIso_comp {κ : Type u} [Finite κ] (ρ : κ → ι) :
    (splitCoverBaseChangeIso h κ).hom ≫ splitCoverMap V ρ =
      (finiteEtaleBaseChange h).map (splitCoverMap P ρ) ≫ (splitCoverBaseChangeIso h ι).hom := by
  refine MorphismProperty.Over.Hom.ext ?_
  change (splitCoverPullbackIso h κ).hom ≫ sigmaIndexMap V ρ =
    ((Over.pullback h).map ((finiteEtaleOverForgetOver P).map (splitCoverMap P ρ))).left ≫
      (splitCoverPullbackIso h ι).hom
  have key : (splitCoverPullbackIso h κ).inv ≫
      ((Over.pullback h).map ((finiteEtaleOverForgetOver P).map (splitCoverMap P ρ))).left =
        sigmaIndexMap V ρ ≫ (splitCoverPullbackIso h ι).inv := by
    have hfst : ∀ b : κ, Sigma.ι (fun _ : κ => V) b ≫ (splitCoverPullbackIso h κ).inv ≫
          pullback.fst ((finiteEtaleOverForgetOver P).obj (splitCover P κ)).hom h ≫
            ((finiteEtaleOverForgetOver P).map (splitCoverMap P ρ)).left =
        Sigma.ι (fun _ : κ => V) b ≫ sigmaIndexMap V ρ ≫ (splitCoverPullbackIso h ι).inv ≫
          pullback.fst ((finiteEtaleOverForgetOver P).obj (splitCover P ι)).hom h := by
      intro b
      rw [splitCoverPullbackIso_inv_fst_assoc, ι_sigmaIndexMap_assoc,
        splitCoverPullbackIso_inv_fst]
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (fun t => t ≫ sigmaIndexMap P ρ)
        (Sigma.ι_comp_desc (fun i : κ => h ≫ Sigma.ι (fun _ : κ => P) i) b)) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (fun t => h ≫ t) (ι_sigmaIndexMap P ρ b)) ?_
      exact (Sigma.ι_comp_desc (fun i : ι => h ≫ Sigma.ι (fun _ : ι => P) i) (ρ b)).symm
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
      exact Sigma.hom_ext _ _ hfst
    · simp only [Category.assoc, baseChange_left_comp_snd]
      refine Sigma.hom_ext _ _ fun j => ?_
      simp [ι_sigmaIndexMap_assoc]
  simpa using congrArg (fun t => (splitCoverPullbackIso h κ).hom ≫ t ≫
    (splitCoverPullbackIso h ι).hom) key.symm

end SplitBaseChange

/-! ### The coequalizer over a base where the two covers split -/

section Split

variable {X P : Scheme.{u}} (g : P ⟶ X) {Y Z : FiniteEtaleOver X} {a b : Y ⟶ Z}
  {ι κ : Type u} [Finite ι] [Finite κ] {σ τ : κ → ι}
  {eY : (finiteEtaleBaseChange g).obj Y ≅ splitCover P κ}
  {eZ : (finiteEtaleBaseChange g).obj Z ≅ splitCover P ι}

/-- If the trivializations `eY` and `eZ` carry the base change of `a` to the index-induced
morphism `splitCoverMap P σ`, then their inverses carry `splitCoverMap P σ` back to it. -/
theorem inv_comp_map_baseChange (h : eY.hom ≫ splitCoverMap P σ =
    (finiteEtaleBaseChange g).map a ≫ eZ.hom) :
    eY.inv ≫ (finiteEtaleBaseChange g).map a = splitCoverMap P σ ≫ eZ.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The cofork on the base changes of `a` and `b` obtained from the split cofork by transport
along the trivializations. -/
def splitCoforkOfIso (ha : eY.hom ≫ splitCoverMap P σ =
      (finiteEtaleBaseChange g).map a ≫ eZ.hom)
    (hb : eY.hom ≫ splitCoverMap P τ = (finiteEtaleBaseChange g).map b ≫ eZ.hom) :
    Cofork ((finiteEtaleBaseChange g).map a) ((finiteEtaleBaseChange g).map b) :=
  Cofork.ofπ (eZ.hom ≫ (splitCoverCofork P σ τ).π) (by
    rw [← Category.assoc, ← ha, ← Category.assoc, ← hb, Category.assoc, Category.assoc]
    exact congrArg (fun t => eY.hom ≫ t) (splitCoverCofork P σ τ).condition)

/-- The transported split cofork is a coequalizer of the base changes of `a` and `b`. -/
def isColimitSplitCoforkOfIso (ha : eY.hom ≫ splitCoverMap P σ =
      (finiteEtaleBaseChange g).map a ≫ eZ.hom)
    (hb : eY.hom ≫ splitCoverMap P τ = (finiteEtaleBaseChange g).map b ≫ eZ.hom) :
    IsColimit (splitCoforkOfIso g ha hb) :=
  Cofork.isColimitOfIsos (splitCoverCofork P σ τ) (isColimit_splitCoverCofork P σ τ) _
    eY.symm eZ.symm (Iso.refl _) (inv_comp_map_baseChange g ha) (inv_comp_map_baseChange g hb)
    (by rw [Iso.refl_hom]; exact congrArg (fun t => eZ.hom ≫ t) (Category.comp_id _))

/-- **The coequalizer of two morphisms of finite étale covers of `X` is a coequalizer of schemes
over a flat base change on which both covers split and both morphisms are index-induced.** This
is the local statement of Stacks Tag 0BNA, for the base-changed coforks of Tag 0BMN. -/
def isColimitBaseChangeCoforkOfSplit [Flat g] (c : Cofork a b) (hc : IsColimit c)
    (ha : eY.hom ≫ splitCoverMap P σ = (finiteEtaleBaseChange g).map a ≫ eZ.hom)
    (hb : eY.hom ≫ splitCoverMap P τ = (finiteEtaleBaseChange g).map b ≫ eZ.hom)
    {S : Scheme.{u}} {s : S ⟶ c.pt.left} {q : S ⟶ P} (hs : IsPullback s q c.pt.hom g) :
    IsColimit (baseChangeCofork a.left b.left c.π.left
      (congrArg (fun k => k.left) c.condition) s) := by
  refine isColimitBaseChangeCoforkOfIsColimitCoforkLeft g a b c hs ?_
  have hcP := isColimitCoforkBaseChange g a b c hc
  have hsp := isColimitSplitCoforkOfIso g ha hb
  have hw : (finiteEtaleBaseChange g).map c.π ≫ (hcP.coconePointUniqueUpToIso hsp).hom =
      eZ.hom ≫ (splitCoverCofork P σ τ).π :=
    hcP.comp_coconePointUniqueUpToIso_hom hsp WalkingParallelPair.one
  have hw' : eZ.hom ≫ (splitCoverCofork P σ τ).π ≫
      (hcP.coconePointUniqueUpToIso hsp).inv = (finiteEtaleBaseChange g).map c.π := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ (hcP.coconePointUniqueUpToIso hsp).inv) hw.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun t => (finiteEtaleBaseChange g).map c.π ≫ t)
      (Iso.hom_inv_id _)) ?_
    exact Category.comp_id _
  refine Cofork.isColimitOfIsos (coforkLeft (splitCoverCofork P σ τ))
    (isColimit_coforkLeft_splitCoverCofork P σ τ) _
    ((finiteEtaleOverForget P).mapIso eY).symm ((finiteEtaleOverForget P).mapIso eZ).symm
    ((finiteEtaleOverForget P).mapIso (hcP.coconePointUniqueUpToIso hsp)).symm
    (congrArg (fun t => (finiteEtaleOverForget P).map t) (inv_comp_map_baseChange g ha))
    (congrArg (fun t => (finiteEtaleOverForget P).map t) (inv_comp_map_baseChange g hb))
    (congrArg (fun t => (finiteEtaleOverForget P).map t) hw')

end Split

end Stacks.FundamentalGroup

end
