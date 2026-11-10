module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmashAwayFromClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GluedDiagonalRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# Completions and morphisms: a morphism étale outside a closed subset (Stacks 0AR9)

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`, let
`T ⊆ |X|` be closed with open complement `U`, and let `f : X' ⟶ X` be a morphism of algebraic
spaces which is locally of finite type and étale outside of `T`, that is, whose restriction
`U' = f⁻¹U ⟶ U` is étale.

**Stacks 0AR9** says that `f` factors as `X' ⟶ X'' ⟶ X` with `X'' ⟶ X` locally of finite type
and an isomorphism over `U`, and with `X'_{/T} ⟶ X''_{/T}` an isomorphism of completions.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factorization_of_isEtale_openComplementRestriction`:
  **Stacks 0AR9**.

## Implementation notes

The proof is the source's. After replacing `X'` by `A = X' ⨿ U`, the restriction
`A_U = A ×_X U ⟶ U` is étale and has a section, so is surjective. The relation
`R = A ⨿_{A_U} (A_U ×_U A_U)` of the source is realized as the subsheaf
`AlgebraicGeometry.Space.gluedDiagonalRelation` of `A ×_X A`: the fppf sheafification of the union
of the diagonal and of the part of `A ×_X A` over `U`. It is an algebraic space by the
open-covering criterion Stacks 02WR, an equivalence relation, and its two projections are étale
(`StacksFrontier.AlgebraicGeometry.Spaces.GluedDiagonalRelation`). The quotient `X'' = A/R` is an
algebraic space by condition (1) of Stacks 04S6,
`AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`.

The three conclusions are the ones of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SmashAwayFromClosed` applied to this relation:
`X'' ⟶ X`
is locally of finite type because `A ⟶ X` is; over `U` the relation is the full kernel pair of the
surjection `A_U ⟶ U`, so `X''` is `U` there; and every section of `R` over `T` is a section of the
diagonal, so the completion of `A ⟶ X''` along `T` is an isomorphism. The completion of `X' ⟶ A`
along `T` is an isomorphism too, the summand `U` having no points over `T`; composing gives the
conclusion for `X' ⟶ X''`.

The hypothesis of the source that `X` be locally Noetherian is not used by the proof, so the
statement is given without it.

## References

* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections over `T` and over the complement of `T` -/

/-- An object of the site carrying a section of `X` which lies over `T` and over the open
complement of `T` has no points. -/
theorem isEmpty_of_hasImageIn_of_mem_openSubspaceOfPoints_compl
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    {V : BigFppfOver B S hS} {x : X.obj (op V)} (hT : Space.HasImageIn B S hS X T V x)
    (hTc : x ∈ (Space.openSubspaceOfPoints B S hS X Tᶜ).obj (op V)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨w, -⟩ := Space.surjective_pointsToScheme B S hS V y
  rw [Space.hasImageIn_iff_range_subset] at hT
  exact hTc ⟨w, rfl⟩ (hT ⟨w, rfl⟩)

/-- Two sections of an fppf sheaf over an object of the site without points agree. -/
theorem eq_of_isEmpty {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {V : BigFppfOver B S hS}
    (hV : IsEmpty ((BigFppfOver.toScheme B S hS).obj V)) (a b : F.obj (op V)) : a = b := by
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF _ (BigFppfOver.bot_mem_topology V hV)).isSeparatedFor.ext fun _ _ h => h.elim

/-! ### Adjoining the open complement to the source -/

/-- If a subfunctor has top sheafification, the sieve on which a given section lies in it is
covering. -/
private theorem sieveOfSection_mem_of_sheafify_eq_top {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : Subfunctor F} (hG : G.sheafify (BigFppfOver.topology B S hS) = ⊤)
    {V : (BigFppfOver B S hS)ᵒᵖ} (a : F.obj V) :
    G.sieveOfSection a ∈ BigFppfOver.topology B S hS V.unop :=
  show a ∈ (G.sheafify (BigFppfOver.topology B S hS)).obj V by rw [hG]; trivial

/-- **Étaleness over `W` of a source covered by `X'` and `W`.** Let `ι₁ : X' ⟶ A` and
`ι₂ : W ⟶ A` be open immersions over `X`, together covering `A` locally. If `X' ⟶ X` is étale
over the open subspace `W`, so is `A ⟶ X`. -/
private theorem isEtale_fromPreimage_of_cover {X X' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hA : IsAlgebraicSpace B S hS A) (W : Subfunctor X) (hW : Space.IsOpenSubspace B S hS W)
    (f : X' ⟶ X) (fA : A ⟶ X) (ι₁ : X' ⟶ A) (ι₂ : W.toFunctor ⟶ A) (h₁ : ι₁ ≫ fA = f)
    (h₂ : ι₂ ≫ fA = W.ι) (hι₁ : Space.IsOpenImmersion B S hS ι₁)
    (hι₂ : Space.IsOpenImmersion B S hS ι₂)
    (hcov : (Subfunctor.range ι₁ ⊔ Subfunctor.range ι₂).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    (het : Space.IsEtale B S hS (W.fromPreimage f)) :
    Space.IsEtale B S hS (W.fromPreimage fA) := by
  have hAW : Space.IsOpenSubspace B S hS (W.preimage fA) :=
    Space.isOpenSubspace_preimage B S hS fA W hX hA hW
  have hX'W : Space.IsOpenSubspace B S hS (W.preimage f) :=
    Space.isOpenSubspace_preimage B S hS f W hX hX' hW
  let κ₁ : (W.preimage f).toFunctor ⟶ (W.preimage fA).toFunctor :=
    Subfunctor.lift ((W.preimage f).ι ≫ ι₁) (by
      rintro V _ ⟨x, rfl⟩
      change fA.app V (ι₁.app V x.1) ∈ W.obj V
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, h₁]
      exact x.2)
  let κ₂ : W.toFunctor ⟶ (W.preimage fA).toFunctor :=
    Subfunctor.lift ι₂ (by
      rintro V _ ⟨w, rfl⟩
      change fA.app V (ι₂.app V w) ∈ W.obj V
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, h₂]
      exact w.2)
  have hκ₁ : κ₁ ≫ W.fromPreimage fA = W.fromPreimage f := by
    rw [← cancel_mono W.ι, Category.assoc, Subfunctor.fromPreimage_ι,
      Subfunctor.fromPreimage_ι]
    change ((W.preimage f).ι ≫ ι₁) ≫ fA = _
    rw [Category.assoc, h₁]
  have hκ₂ : κ₂ ≫ W.fromPreimage fA = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, Subfunctor.fromPreimage_ι, Category.id_comp]
    exact h₂
  refine Space.isEtale_of_isEtale_comp_of_two_opens B S hS hAW.1 hW.1 hX'W.1 hW.1 κ₁ κ₂ ?_ ?_
    ?_ _ (by rwa [hκ₁]) (by rw [hκ₂]; exact Space.isEtale_of_isIso B S hS _)
  · exact Space.isOpenImmersion_of_comp_mono B S hS κ₁ (W.preimage fA).ι
      (Space.isOpenImmersion_comp B S hS (W.preimage f).ι ι₁ hX'W.2 hι₁)
  · exact Space.isOpenImmersion_of_comp_mono B S hS κ₂ (W.preimage fA).ι hι₂
  · refine eq_top_iff.2 fun V a _ => ?_
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieveOfSection_mem_of_sheafify_eq_top B S hS hcov a.1)
    rintro V' q (⟨x, hx⟩ | ⟨w, hw⟩)
    · have hxW : x ∈ (W.preimage f).obj (op V') := by
        change f.app (op V') x ∈ W.obj (op V')
        rw [← h₁, NatTrans.comp_app, ConcreteCategory.comp_apply, hx]
        exact ((W.preimage fA).toFunctor.map q.op a).2
      exact Or.inl ⟨⟨x, hxW⟩, Subtype.ext hx⟩
    · exact Or.inr ⟨w, Subtype.ext hw⟩

/-- **The replacement of `X'` by `X' ⨿ U` in the proof of Stacks 0AR9.** Let `f : X' ⟶ X` be a
morphism of algebraic spaces, locally of finite type and étale over an open subspace `W` of `X`.
The coproduct `A = X' ⨿ W` with the morphism `A ⟶ X` induced by `f` and the inclusion of `W` is an
algebraic space, `A ⟶ X` is locally of finite type and étale over `W`, the two summands cover `A`
locally, and the inclusion of `X'` is a monomorphism. -/
theorem exists_coproduct_isEtale_fromPreimage {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (W : Subfunctor X) (hW : Space.IsOpenSubspace B S hS W) (f : X' ⟶ X)
    (hft : Space.IsLocallyOfFiniteType B S hS f) (het : Space.IsEtale B S hS (W.fromPreimage f)) :
    ∃ (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS A) (ιX' : X' ⟶ A)
      (ιW : W.toFunctor ⟶ A) (fA : A ⟶ X), ιX' ≫ fA = f ∧ ιW ≫ fA = W.ι ∧ Mono ιX' ∧
      Space.IsLocallyOfFiniteType B S hS fA ∧ Space.IsEtale B S hS (W.fromPreimage fA) ∧
      (Subfunctor.range ιX' ⊔ Subfunctor.range ιW).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let F₁ : Sheaf J (Type u) := ⟨X', hX'.isSheaf⟩
  let F₂ : Sheaf J (Type u) := ⟨W.toFunctor, hW.1.isSheaf⟩
  let FX : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  let Fs : WalkingPair → Sheaf J (Type u) := pairFunction F₁ F₂
  have hFs : ∀ k, IsAlgebraicSpace B S hS (Fs k).obj := fun k => WalkingPair.casesOn k hX' hW.1
  let E := colimit.cocone (Discrete.functor Fs ⋙ sheafToPresheaf J (Type u))
  let G := Sheaf.sheafifyCocone E
  have hG : IsColimit G := Sheaf.isColimitSheafifyCocone E (colimit.isColimit _)
  have hA : IsAlgebraicSpace B S hS G.pt.obj :=
    Space.isAlgebraicSpace_finiteCoproduct B S hS (fun k => (Fs k).obj) hFs G.pt
      (fun k => G.ι.app ⟨k⟩) hG
  let m : ∀ k, Fs k ⟶ FX := fun k => WalkingPair.casesOn k
    (ObjectProperty.homMk f) (ObjectProperty.homMk W.ι)
  let fS : G.pt ⟶ FX := hG.desc (Cofan.mk FX m)
  have hfS : ∀ k, (G.ι.app ⟨k⟩).hom ≫ fS.hom = (m k).hom := fun k =>
    congrArg (fun g => g.hom) (hG.fac (Cofan.mk FX m) ⟨k⟩)
  let ι₁ : X' ⟶ G.pt.obj := (G.ι.app ⟨.left⟩).hom
  let ι₂ : W.toFunctor ⟶ G.pt.obj := (G.ι.app ⟨.right⟩).hom
  let fA : G.pt.obj ⟶ X := fS.hom
  have h₁ : ι₁ ≫ fA = f := hfS .left
  have h₂ : ι₂ ≫ fA = W.ι := hfS .right
  have hopen : ∀ k, Space.IsOpenImmersion B S hS (G.ι.app ⟨k⟩).hom := fun k =>
    coproductIncl_isOpenImmersion B S hS Fs G.pt (fun k => G.ι.app ⟨k⟩) hG k
  have hcov : (Subfunctor.range ι₁ ⊔ Subfunctor.range ι₂).sheafify J = ⊤ := by
    have hle : (⨆ k, Subfunctor.range (G.ι.app ⟨k⟩).hom) ≤
        Subfunctor.range ι₁ ⊔ Subfunctor.range ι₂ := by
      refine iSup_le fun k => ?_
      cases k
      · exact le_sup_left
      · exact le_sup_right
    exact eq_top_iff.2 ((Space.sheafify_iSup_range_hom_of_isColimit B S hS
      (fun k => G.ι.app ⟨k⟩) hG).symm.le.trans fun V x hx =>
        (BigFppfOver.topology B S hS).superset_covering (fun _ _ h' => hle _ h') hx)
  refine ⟨G.pt.obj, hA, ι₁, ι₂, fA, h₁, h₂,
    Space.mono_of_isOpenImmersion B S hS _ (hopen .left), ?_, ?_, hcov⟩
  · refine Space.isLocallyOfFiniteType_of_isColimit_cofan B S hS (fun k => G.ι.app ⟨k⟩) hG hFs
      hA hX fA fun k => ?_
    cases k
    · exact (hfS .left).symm ▸ hft
    · exact (hfS .right).symm ▸ Space.isLocallyOfFiniteType_of_isEtale' B S hS _
        (Space.isEtale_ι_of_isOpenSubspace hW)
  · -- étaleness over `W`, checked on the two summands
    exact isEtale_fromPreimage_of_cover B S hS hX hX' hA W hW f fA ι₁ ι₂ h₁ h₂ (hopen .left)
      (hopen .right) hcov het

/-! ### The relation over `T` and over its complement -/

section Relation

variable {X A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fA : A ⟶ X) (T : Set (Space.points B S hS X))

/-- **Every section of the relation lying over `T` is a section of the diagonal**: this is the
source's "the completion of `R` along the inverse image of `T` is that of `A`". Locally a section
of the relation lies on the diagonal or over the complement of `T`, and an object of the site
carrying a section over `T` and over its complement has no points. -/
theorem gluedRelation_source_eq_target_of_hasImageIn
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A) {V : BigFppfOver B S hS}
    (r : (Space.gluedDiagonalRelation fA (Space.openSubspaceOfPoints B S hS X Tᶜ)).toFunctor.obj
      (op V))
    (h : Space.HasImageIn B S hS X T V (fA.app _ ((pullback.fst fA fA).app _ r.1))) :
    (pullback.snd fA fA).app _ r.1 = (pullback.fst fA fA).app _ r.1 := by
  refine (((isSheaf_iff_isSheaf_of_type _ _).1 hA) _ r.2).isSeparatedFor.ext fun V' q hq => ?_
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  rcases hq with h' | h'
  · exact h'.symm
  · refine eq_of_isEmpty B S hS hA ?_ _ _
    refine isEmpty_of_hasImageIn_of_mem_openSubspaceOfPoints_compl B S hS T ?_ h'
    have hres := (Space.completionSubfunctor B S hS X T).map q.op
      (show ULift.up (fA.app _ ((pullback.fst fA fA).app _ r.1)) ∈
        (Space.completionSubfunctor B S hS X T).obj (op V) from h)
    change Space.HasImageIn B S hS X T V'
      (X.map q.op (fA.app _ ((pullback.fst fA fA).app _ r.1))) at hres
    rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply] at hres

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Sections of `A` with the same image in `W` have the same image in the quotient**: the
relation contains every pair of sections of `A` with the same image in `W`. -/
private theorem toQuotientSheaf_gluedRelation_app_eq {W : Subfunctor X} {V : (BigFppfOver B S hS)ᵒᵖ}
    (a b : A.obj V) (hab : fA.app V a = fA.app V b) (ha : fA.app V a ∈ W.obj V) :
    (Space.toQuotientSheaf (Space.gluedRelation fA W)).app V a =
      (Space.toQuotientSheaf (Space.gluedRelation fA W)).app V b := by
  obtain ⟨x, hx₁, hx₂⟩ := Types.exists_of_isPullback ((IsPullback.of_hasPullback fA fA).map
    ((evaluation _ _).obj V)) a b hab
  have hx₁' : (pullback.fst fA fA).app V x = a := hx₁
  have hx₂' : (pullback.snd fA fA).app V x = b := hx₂
  have hmem : x ∈ (Space.gluedDiagonalRelation fA W).obj V :=
    Space.mem_gluedDiagonalRelation_of_mem fA W (by rwa [hx₁'])
  have key := congrArg (fun k => k.app V ⟨x, hmem⟩)
    (Space.target_toQuotientSheaf_eq_source (Space.gluedRelation fA W))
  rw [Space.gluedRelation_target_left, Space.gluedRelation_source_left] at key
  simp only [NatTrans.comp_app] at key
  change (Space.toQuotientSheaf (Space.gluedRelation fA W)).app V ((pullback.fst fA fA).app V x) =
    (Space.toQuotientSheaf (Space.gluedRelation fA W)).app V ((pullback.snd fA fA).app V x) at key
  rwa [hx₁', hx₂'] at key

/-- **The quotient is an isomorphism over `W`.** The relation contains every pair of sections of
`A` with the same image in `W`, so a section `W ⟶ A` of `A ⟶ X` over `W` descends to an inverse of
the base change of `A/R ⟶ X` to `W`. -/
theorem isIso_pullback_snd_quotientSheafToBase_gluedRelation
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (W : Subfunctor X)
    (ιW : W.toFunctor ⟶ A) (hιW : ιW ≫ fA = W.ι) :
    IsIso (pullback.snd (Space.quotientSheafToBase hX (Space.gluedRelation fA W)).hom W.ι) := by
  let q := Space.toQuotientSheaf (Space.gluedRelation fA W)
  let hh := (Space.quotientSheafToBase hX (Space.gluedRelation fA W)).hom
  have hqh : q ≫ hh = fA := Space.toQuotientSheaf_quotientSheafToBase hX _
  let σ : W.toFunctor ⟶ (Space.quotientSheaf (Space.gluedRelation fA W)).obj := ιW ≫ q
  have hσ : σ ≫ hh = W.ι := by
    change (ιW ≫ q) ≫ hh = W.ι
    rw [Category.assoc, hqh, hιW]
  have key : pullback.snd hh W.ι ≫ σ = pullback.fst hh W.ι := by
    have hQsep := (isSheaf_iff_isSheaf_of_type _ _).1
      (Space.quotientSheaf (Space.gluedRelation fA W)).property
    have := Space.isLocallySurjective_toQuotientSheaf (Space.gluedRelation fA W)
    ext V z
    let y := (pullback.fst hh W.ι).app V z
    let w := (pullback.snd hh W.ι).app V z
    have hyw : hh.app V y = W.ι.app V w := by
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
        congrArg (fun k => k.app V z) (pullback.condition (f := hh) (g := W.ι))
    refine (hQsep _ (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) q y)).isSeparatedFor.ext
      fun V' g hg => ?_
    obtain ⟨a, ha⟩ := hg
    change (Space.quotientSheaf (Space.gluedRelation fA W)).obj.map g.op (σ.app V w) =
      (Space.quotientSheaf (Space.gluedRelation fA W)).obj.map g.op y
    rw [← ha, ← NatTrans.naturality_apply]
    change q.app (op V') (ιW.app (op V') (W.toFunctor.map g.op w)) = q.app (op V') a
    have hfa : fA.app (op V') a = W.ι.app (op V') (W.toFunctor.map g.op w) := by
      rw [← hqh, NatTrans.comp_app, ConcreteCategory.comp_apply, ha, NatTrans.naturality_apply,
        hyw, NatTrans.naturality_apply]
    have hfw : fA.app (op V') (ιW.app (op V') (W.toFunctor.map g.op w)) =
        W.ι.app (op V') (W.toFunctor.map g.op w) := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hιW]
    refine toQuotientSheaf_gluedRelation_app_eq B S hS fA _ _ (hfw.trans hfa.symm) ?_
    rw [hfw]
    exact (W.toFunctor.map g.op w).2
  refine ⟨⟨pullback.lift σ (𝟙 _) (by rw [hσ, Category.id_comp]), ?_, pullback.lift_snd _ _ _⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, key, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

end Relation

/-! ### The completion of the summand `X'` -/

/-- **The completion of a composite.** If the completions of `g₁` and `g₂` along the inverse
images of `P` are locally injective and locally surjective, so is that of `g₁ ≫ g₂`. -/
private theorem isLocallyBijective_completionMap_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (P : Set (Space.points B S hS Z))
    [Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS g₁ (Space.pointsMap B S hS Y g₂ ⁻¹' P))]
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS g₁ (Space.pointsMap B S hS Y g₂ ⁻¹' P))]
    [Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) (Space.completionMap B S hS g₂ P)]
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMap B S hS g₂ P)] :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
        (Space.completionMap B S hS (g₁ ≫ g₂) P) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Space.completionMap B S hS (g₁ ≫ g₂) P) := by
  have hset : Space.pointsMap B S hS X (g₁ ≫ g₂) ⁻¹' P =
      Space.pointsMap B S hS X g₁ ⁻¹' (Space.pointsMap B S hS Y g₂ ⁻¹' P) := by
    rw [Space.pointsMap_comp]
    rfl
  let e := Subfunctor.homOfLe (le_of_eq (congrArg (Space.completionSubfunctor B S hS X) hset))
  have hfac : Space.completionMap B S hS (g₁ ≫ g₂) P =
      e ≫ Space.completionMap B S hS g₁ _ ≫ Space.completionMap B S hS g₂ P := rfl
  have : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) e :=
    Presheaf.isLocallyInjective_of_injective _ _ fun V x y hxy =>
      Subtype.ext (congrArg Subtype.val hxy)
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) e :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun V y =>
      ⟨⟨y.1, by rw [congrArg (Space.completionSubfunctor B S hS X) hset]; exact y.2⟩, rfl⟩
  rw [hfac]
  exact ⟨inferInstance, inferInstance⟩

/-- **The summand `X'` of `X' ⨿ U` has the same completion along `T`.** Let `ι₁ : X' ⟶ A` be a
monomorphism and `ιW : W ⟶ A` a morphism from the complement of `T` over `X`, together covering
`A` locally. Then the completion of `ι₁` along any set of points of `A` lying over `T` is an
isomorphism: a section of `A` over `T` lies locally in `X'`, the pieces where it lies in `W` having
no points. -/
theorem isLocallyBijective_completionMap_of_cover {X X' A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (fA : A ⟶ X) (T : Set (Space.points B S hS X)) (ι₁ : X' ⟶ A) [Mono ι₁]
    (ιW : (Space.openSubspaceOfPoints B S hS X Tᶜ).toFunctor ⟶ A)
    (hιW : ιW ≫ fA = (Space.openSubspaceOfPoints B S hS X Tᶜ).ι)
    (hcov : (Subfunctor.range ι₁ ⊔ Subfunctor.range ιW).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    (S' : Set (Space.points B S hS A)) (hS' : S' ⊆ Space.pointsMap B S hS A fA ⁻¹' T) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS) (Space.completionMap B S hS ι₁ S') ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
        (Space.completionMap B S hS ι₁ S') := by
  refine ⟨Presheaf.isLocallyInjective_of_injective _ _ fun V x₁ x₂ hx => ?_, ⟨fun {V} y => ?_⟩⟩
  · have hinj : Function.Injective (ι₁.app V) :=
      (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app ι₁).1 inferInstance V)
    exact Subtype.ext (ULift.ext (hinj (congrArg (fun z => z.1.down) hx)))
  · obtain ⟨⟨a⟩, ha⟩ := y
    refine (BigFppfOver.topology B S hS).transitive
      (sieveOfSection_mem_of_sheafify_eq_top B S hS hcov a) _ fun V' q hq => ?_
    rcases hq with ⟨x, hx⟩ | ⟨w, hw⟩
    · refine (BigFppfOver.topology B S hS).superset_covering ?_
        ((BigFppfOver.topology B S hS).top_mem V')
      intro V'' q' _
      refine ⟨⟨ULift.up (X'.map q'.op x), ?_⟩, ?_⟩
      · refine (hasImageIn_preimage_pointsMap_iff B S hS ι₁ S' V'' _).2 ?_
        rw [NatTrans.naturality_apply, hx]
        exact (Space.completionSubfunctor B S hS A S').map q'.op
          ((Space.completionSubfunctor B S hS A S').map q.op ha)
      · apply Subtype.ext
        apply ULift.ext
        change ι₁.app (op V'') (X'.map q'.op x) = A.map (q' ≫ q).op a
        rw [NatTrans.naturality_apply, hx, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    · -- over the complement of `T` the object has no points
      have hrestr : Space.HasImageIn B S hS A S' V' (A.map q.op a) :=
        (Space.completionSubfunctor B S hS A S').map q.op ha
      have hT : Space.HasImageIn B S hS X T V' (fA.app _ (A.map q.op a)) :=
        (hasImageIn_preimage_pointsMap_iff B S hS fA T V' _).1 fun p => hS' (hrestr p)
      have hTc : fA.app _ (A.map q.op a) ∈
          (Space.openSubspaceOfPoints B S hS X Tᶜ).obj (op V') := by
        rw [← hw, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hιW]
        exact w.2
      exact (BigFppfOver.topology B S hS).superset_covering bot_le
        (BigFppfOver.bot_mem_topology V'
          (isEmpty_of_hasImageIn_of_mem_openSubspaceOfPoints_compl B S hS T hT hTc))

/-! ### Stacks 0AR9 -/

/-- If the restriction of `f` to the open complement of `T` is étale, so is the morphism from the
inverse image of that open subspace to it. -/
private theorem isEtale_fromPreimage_openSubspaceOfPoints_compl
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) (f : X' ⟶ X)
    (hW : Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T)) :
    Space.IsEtale B S hS ((Space.openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f) := by
  refine Space.isEtale_of_comp_mono B S hS _ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι ?_
  rw [Subfunctor.fromPreimage_ι, Space.preimage_openSubspaceOfPoints,
    ← Space.openComplementRestriction_ι]
  exact Space.isEtale_comp B S hS het (Space.isEtale_ι_of_isOpenSubspace hW)

/-- **The quotient by the glued relation is an algebraic space**, by condition (1) of Stacks 04S6:
the relation is an algebraic space and its two projections are étale. -/
private theorem isAlgebraicSpace_quotientSheaf_gluedRelation {X A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fA : A ⟶ X} {W : Subfunctor X} (H : Space.GluedRelationData B S hS fA W) :
    letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
    IsAlgebraicSpace B S hS (Space.quotientSheaf (Space.gluedRelation fA W)).obj := by
  refine Space.bootstrap04S6QuotientSheaf B S hS _ H.isAlgebraicSpace_gluedDiagonalRelation
    H.isAlgebraicSpace_source (Space.isEquivalenceRelation_gluedRelation fA W) ?_ ?_ ?_ ?_
  · rw [Space.gluedRelation_target_left]
    exact Space.isFlat_of_isEtale B S hS H.isEtale_target
  · rw [Space.gluedRelation_target_left]
    exact Space.isLocallyOfFinitePresentation_of_isEtale B S hS H.isEtale_target
  · rw [Space.gluedRelation_source_left]
    exact Space.isFlat_of_isEtale B S hS H.isEtale_source
  · rw [Space.gluedRelation_source_left]
    exact Space.isLocallyOfFinitePresentation_of_isEtale B S hS H.isEtale_source

/-- **Stacks 0AR9.** Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic
space over `S` and let `T ⊆ |X|` be closed. Let `f : X' ⟶ X` be a morphism of algebraic spaces
which is locally of finite type and étale outside of `T`, i.e. whose restriction
`U' = f⁻¹U ⟶ U` to the open subspace `U` with `|U| = |X| ∖ T` is étale. Then `f` factors as
`X' ⟶ X'' ⟶ X` where

* `X''` is an algebraic space and `X'' ⟶ X` is locally of finite type,
* `X'' ⟶ X` is an isomorphism over `U`: its base change to `U` is an isomorphism, and
* `X'_{/T} ⟶ X''_{/T}` is an isomorphism, the completion of `X' ⟶ X''` along the inverse image
  of `T` in the sense of Section 0GDB, `AlgebraicGeometry.Space.completionSheafMap`.

The source assumes moreover that `X` is locally Noetherian; its proof does not use that
hypothesis, so it is dropped here. -/
@[stacks 0AR9 "stated without the hypothesis that X be locally Noetherian, which the source's \
proof does not use; X'' ⟶ X is an isomorphism over U in the form that its base change to the \
open subspace with point set |X| ∖ T is an isomorphism, and the completions are the \
completionSheafMap of Section 0GDB"]
theorem exists_factorization_of_isEtale_openComplementRestriction
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hX' : IsAlgebraicSpace B S hS X') (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (f : X' ⟶ X) (hft : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T)) :
    ∃ (X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X'')
      (g : X' ⟶ X'') (h : X'' ⟶ X), g ≫ h = f ∧ Space.IsLocallyOfFiniteType B S hS h ∧
        IsIso (pullback.snd h (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) ∧
        IsIso (Space.completionSheafMap B S hS g (Space.pointsMap B S hS X'' h ⁻¹' T)) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  have hW : Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ) :=
    Space.isOpenSubspace_openSubspaceOfPoints_compl_of_isClosed B S hS hX T hT
  -- étaleness of `U' ⟶ U`, read on the inverse image of `U`
  have hetf := isEtale_fromPreimage_openSubspaceOfPoints_compl B S hS T f hW het
  -- replace `X'` by `X' ⨿ U`
  obtain ⟨A, hA, ι₁, ιW, fA, h₁, h₂, hmono, hfAft, hfAet, hcov⟩ :=
    exists_coproduct_isEtale_fromPreimage B S hS hX hX' _ hW f hft hetf
  have H : Space.GluedRelationData B S hS fA (Space.openSubspaceOfPoints B S hS X Tᶜ) :=
    ⟨hA, hX, hW, hfAet⟩
  -- the quotient by the glued relation
  set j := Space.gluedRelation fA (Space.openSubspaceOfPoints B S hS X Tᶜ) with hjdef
  have hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf j).obj :=
    isAlgebraicSpace_quotientSheaf_gluedRelation B S hS H
  set q := Space.toQuotientSheaf j
  set hh := (Space.quotientSheafToBase hX.isSheaf j).hom
  have hqh : q ≫ hh = fA := Space.toQuotientSheaf_quotientSheafToBase hX.isSheaf j
  refine ⟨(Space.quotientSheaf j).obj, hQ, ι₁ ≫ q, hh, by rw [Category.assoc, hqh, h₁],
    isLocallyOfFiniteType_quotientSheafToBase B S hS hX hA j hQ hfAft,
    isIso_pullback_snd_quotientSheafToBase_gluedRelation B S hS fA hX.isSheaf _ ιW h₂, ?_⟩
  -- the completions along `T`
  have hj : Space.IsPreEquivalenceRelation j :=
    ((Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1
      (Space.isEquivalenceRelation_gluedRelation fA _)).2
  have hdiag : ∀ (V : BigFppfOver B S hS) (r : (Space.gluedArrows fA
      (Space.openSubspaceOfPoints B S hS X Tᶜ)).left.obj (op V)),
      Space.HasImageIn B S hS X T V ((Space.gluedArrows fA
        (Space.openSubspaceOfPoints B S hS X Tᶜ)).hom.app (op V) r) →
        j.source.left.app (op V) r = j.target.left.app (op V) r := by
    intro V r hr
    rw [hjdef, Space.gluedRelation_source_left, Space.gluedRelation_target_left]
    exact gluedRelation_source_eq_target_of_hasImageIn B S hS fA T hA.isSheaf r hr
  have := isLocallySurjective_completionMap_toQuotientSheaf B S hS j
    (Space.pointsMap B S hS _ hh ⁻¹' T)
  have := isLocallyInjective_completionMap_toQuotientSheaf B S hS j hj T hh hqh hdiag
  obtain ⟨_, _⟩ := isLocallyBijective_completionMap_of_cover B S hS fA T ι₁ ιW h₂ hcov
    (Space.pointsMap B S hS A q ⁻¹' (Space.pointsMap B S hS _ hh ⁻¹' T)) (fun x hx => by
      change Space.pointsMap B S hS A fA x ∈ T
      rw [← hqh, Space.pointsMap_comp]
      exact hx)
  obtain ⟨_, _⟩ := isLocallyBijective_completionMap_comp B S hS ι₁ q
    (Space.pointsMap B S hS _ hh ⁻¹' T)
  exact isIso_completionSheafMap_of_isLocallyBijective B S hS _ _

end AlgebraicGeometry.FormalSpace

end
