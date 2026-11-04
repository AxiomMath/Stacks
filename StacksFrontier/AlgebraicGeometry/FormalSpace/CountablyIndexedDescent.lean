module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatOfRepresentableFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismFlatCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSurjectiveFlat
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSurjectiveFlat

/-!
# Countable indexing ascends along a surjective flat morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces, surjective
and flat. If `X` is countably indexed then so is `Y`. Together with clause (1) of
Stacks 0AKQ — the converse, which holds for every morphism representable by algebraic spaces —
this is the equivalence of **Stacks 0AKS**.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isCountablyIndexed_of_surjective_flat`:
  the forward implication of **Stacks 0AKS**.

## Implementation notes

The proof is the source's. Write `X = colim_n X_n` for the sequential presentation of `X` and
`Y = colim_i Y_i` for a presentation of `Y` by affine thickenings over a directed preorder.
Two factorizations of Stacks 0AIA, in the shape
`AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage`, produce a countable family of
indices of the latter and, for each index, a comparison with one of its members:

* each stage `X_n ⟶ Y` factors through some `Y_{λ(n)}`;
* each represented fibre product `Y_i ×_Y X`, which is an affine scheme of the site by
  Stacks 0AKN, factors through some `X_{n(i)}` over `X`.

Composing the two gives, for each `i`, a morphism `Y_i ×_Y X ⟶ Y_{λ(n(i))}` over `Y`. Choosing
an index `k` above both `i` and `λ(n(i))` puts the situation inside the single affine scheme
`Y_k`, where `Y_i` and `Y_{λ(n(i))}` are closed subschemes; the two morphisms `Y_i ×_Y X ⟶ Y_k`
so obtained agree because the stage inclusion `Y_k ⟶ Y` is a monomorphism. Surjectivity and
flatness of `f` make `Γ(Y_i) ⟶ Γ(Y_i ×_Y X)` faithfully flat, hence injective, and an
injective map on sections lets the closed immersion `Y_{λ(n(i))} ⟶ Y_k` absorb `Y_i ⟶ Y_k`:
the ideal cut out by the former is contained in the ideal cut out by the latter. That is the
dotted arrow `Y_i ⟶ Y_{λ(n(i))}` over `Y`.

So every stage of the presentation of `Y` factors through a member of a countable subfamily.
Monotonising the subfamily and using that each stage inclusion is a monomorphism, the
restriction of the presentation to `ℕ` is again a colimit cocone, which is a sequential
presentation of `Y`.

Faithful flatness of the morphism of sections is where surjectivity and flatness are used, and
it is used only through its injectivity. It is obtained over an affine test object: the
represented fibre product is an affine scheme because `f` is representable and affine by
Stacks 0AKN, its projection is flat because flatness of `f` is tested on every étale chart of
every represented base change and the identity charts of an affine base change are among them,
and it is surjective because surjectivity on points is stable under base change (Stacks 0GHR)
and surjectivity on the points of two represented presheaves is surjectivity of the morphism of
schemes.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0GHR](https://stacks.math.columbia.edu/tag/0GHR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Two elementary helpers -/

/-- A sequence in a directed preorder is dominated termwise by a monotone one. -/
private theorem exists_monotone_ge {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (f : ℕ → I) : ∃ g : ℕ → I, Monotone g ∧ ∀ n, f n ≤ g n := by
  classical
  choose upper hleft hright using (fun i j : I => exists_ge_ge i j)
  let g : ℕ → I := fun n => Nat.rec (f 0) (fun n i => upper i (f (n + 1))) n
  refine ⟨g, monotone_nat_of_le_succ (fun n => hleft _ _), ?_⟩
  intro n
  cases n with
  | zero => exact le_rfl
  | succ n => exact hright _ _

/-- A colimit cocone whose legs are monomorphisms stays a colimit cocone after restriction
along a sequence of indices through whose members every leg factors. -/
private noncomputable def isColimit_of_sequence_factors
    {C : Type*} [Category C] {I : Type*} [Category I]
    (D : I ⥤ C) (c : Cocone D) (hc : IsColimit c)
    (s : ℕ ⥤ I) (hm : ∀ i, Mono (c.ι.app i))
    (h : ∀ i, ∃ n, ∃ a : D.obj i ⟶ D.obj (s.obj n), a ≫ c.ι.app (s.obj n) = c.ι.app i) :
    IsColimit (c.whisker s) := by
  classical
  choose n a ha using h
  have key (t : Cocone (s ⋙ D)) {i : I} {m m' : ℕ} (x : D.obj i ⟶ D.obj (s.obj m))
      (y : D.obj i ⟶ D.obj (s.obj m'))
      (h : x ≫ c.ι.app (s.obj m) = y ≫ c.ι.app (s.obj m')) :
      x ≫ t.ι.app m = y ≫ t.ι.app m' := by
    have heq : x ≫ D.map (s.map (homOfLE (le_max_left m m'))) =
        y ≫ D.map (s.map (homOfLE (le_max_right m m'))) := by
      let := hm (s.obj (max m m'))
      apply (cancel_mono (c.ι.app (s.obj (max m m')))).1
      simp only [Category.assoc, c.w, h]
    have h1 := t.w (homOfLE (le_max_left m m'))
    have h2 := t.w (homOfLE (le_max_right m m'))
    simp only [Functor.comp_map] at h1 h2
    rw [← h1, ← h2, ← Category.assoc, heq, Category.assoc]
  let extend (t : Cocone (s ⋙ D)) : Cocone D :=
    { pt := t.pt
      ι := { app := fun i => a i ≫ t.ι.app (n i)
             naturality := fun i j b => by
               simpa using key t (D.map b ≫ a j) (a i) (by simp [ha, c.w]) } }
  have hext (t : Cocone (s ⋙ D)) (j : ℕ) : (extend t).ι.app (s.obj j) = t.ι.app j := by
    simpa using key t (a (s.obj j)) (𝟙 _) (by simp [ha])
  refine { desc := fun t => hc.desc (extend t), fac := ?_, uniq := ?_ }
  · intro t j
    exact (hc.fac (extend t) (s.obj j)).trans (hext t j)
  · intro t m hm'
    apply hc.hom_ext
    intro i
    rw [hc.fac]
    change c.ι.app i ≫ m = a i ≫ t.ι.app (n i)
    rw [← ha i, Category.assoc]
    exact congrArg (a i ≫ ·) (hm' (n i))

/-! ### Absorbing a morphism into a closed immersion -/

/-- Surjectivity on points of presheaves with values in the larger universe transfers across
isomorphisms of the source and of the target. -/
private theorem isSurjectiveULift_of_iso_comm
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {a : F ⟶ G} {a' : F' ⟶ G'} (eF : F' ≅ F) (eG : G' ≅ G)
    (hcomm : a' ≫ eG.hom = eF.hom ≫ a)
    (ha : Space.IsSurjectiveULift.{u + 1} B S hS a) :
    Space.IsSurjectiveULift.{u + 1} B S hS a' := by
  intro y
  obtain ⟨x, hx⟩ := ha (Space.pointsMapULift.{u + 1} B S hS G' eG.hom y)
  obtain ⟨x', rfl⟩ := (Space.bijective_pointsMapULift_of_iso B S hS eF).2 x
  refine ⟨x', (Space.bijective_pointsMapULift_of_iso B S hS eG).1 ?_⟩
  have h1 : Space.pointsMapULift.{u + 1} B S hS F' (a' ≫ eG.hom) x' =
      Space.pointsMapULift.{u + 1} B S hS F' (eF.hom ≫ a) x' := by rw [hcomm]
  rw [Space.pointsMapULift_comp, Space.pointsMapULift_comp] at h1
  exact h1.trans hx

/-! ### Stacks 0AKS, the forward implication -/

/-- **Stacks 0AKS, the forward implication.** Let `f : X ⟶ Y` be a morphism of affine formal
algebraic spaces over `S` which is representable by algebraic spaces, surjective and flat. If
`X` is countably indexed then so is `Y`. -/
@[stacks 0AKS "the implication from the source being countably indexed to the target being \
countably indexed, which is the content of the source's proof; the converse is clause (1) of \
Stacks 0AKQ"]
theorem isCountablyIndexed_of_isCountablyIndexed_of_surjective_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hfrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f)
    (hflat : ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
          (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) g.hom) f.hom hf)
    (hXc : IsCountablyIndexed B S hS X) :
    IsCountablyIndexed B S hS Y := by
  classical
  obtain ⟨hfrep', hflat'⟩ := hflat
  obtain ⟨D_X, hD_X, ⟨eX⟩⟩ := hXc
  obtain ⟨-, I, pre, hI, hdir, D_Y, hD_Y, ⟨eY⟩⟩ := id hY
  let : Preorder I := pre
  have : Nonempty I := hI
  have : IsDirected I (· ≤ ·) := hdir
  let J := BigFppfOver.topology B S hS
  let H := Sheaf.sheafifiedYoneda J
  let inc := BigAffineFppf.inclusion B S hS
  let T := BigFppfOver.toScheme B S hS
  let FX := D_X ⋙ inc ⋙ H
  let G := D_Y ⋙ inc ⋙ H
  let FF := Sheaf.fullyFaithfulSheafifiedYoneda J
  -- Each stage of `X` maps into a stage of `Y`.
  have hsourceStage (n : ℕ) : ∃ (i : I) (g : D_X.obj n ⟶ D_Y.obj i),
      H.map (inc.map g) ≫ colimit.ι G i ≫ eY.inv =
        colimit.ι FX n ≫ eX.inv ≫ f :=
    exists_factor_to_affine_stage B S hS Y I D_Y hD_Y eY (D_X.obj n)
      (colimit.ι FX n ≫ eX.inv ≫ f)
  choose targetIndex targetMap htargetMap using hsourceStage
  -- Stacks 0AKN: `f` is representable by schemes and affine.
  have hfAff := relative_isAffineHom_of_hasThickeningPresentation B S hS f hX.2 hY.2 hfrep
  let hRep := hfAff.1
  -- The stage inclusions of the presentation of `Y` are monomorphisms.
  have hGmono : ∀ i j (g : i ⟶ j), Mono (G.map g) := by
    intro i j g
    let := (hD_Y g).1
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying J T (inc.map (D_Y.map g))
      (by
        change Mono ((BigAffineFppf.toScheme B S hS).map (D_Y.map g))
        infer_instance)
  have hιmono (i : I) : Mono (colimit.ι G i ≫ eY.inv) := by
    let := Sheaf.mono_colimit_ι_of_mono_transition G hGmono i
    infer_instance
  -- For each stage of `Y`, its fibre product with `f` is affine, maps into a stage of `X`,
  -- and its projection is injective on global sections.
  have hfiberStage (i : I) :
      ∃ n : ℕ, ∃ g : H.obj (hRep.pullback (colimit.ι G i ≫ eY.inv)) ⟶ FX.obj n,
        g ≫ colimit.ι FX n ≫ eX.inv = hRep.fst (colimit.ι G i ≫ eY.inv) ∧
        Function.Injective ((T.map (hRep.snd (colimit.ι G i ≫ eY.inv))).appTop).hom := by
    set ξ : G.obj i ⟶ Y := colimit.ι G i ≫ eY.inv with hξdef
    set pb := hRep.pullback ξ with hpbdef
    have hU : IsAffine (T.obj (inc.obj (D_Y.obj i))) := (D_Y.obj i).property
    have hSnd : IsAffineHom (T.map (hRep.snd ξ)) :=
      hfAff.2 ξ (hRep.fst ξ) (hRep.snd ξ) (hRep.isPullback ξ)
    have hpb : IsAffine (T.obj pb) := by
      let : IsAffineHom (T.map (hRep.snd ξ)) := hSnd
      let : IsAffine (T.obj (inc.obj (D_Y.obj i))) := hU
      exact isAffine_of_isAffineHom (T.map (hRep.snd ξ))
    -- Compare the represented fibre product with the chosen pullback of presheaves.
    have hsheafLift : ∀ V : BigFppfOver B S hS,
        Presheaf.IsSheaf J ((uliftYoneda.{u + 1}).obj V) := by
      intro V
      rw [isSheaf_iff_isSheaf_of_type]
      exact Presieve.isSheaf_comp_uliftFunctor _
        ((isSheaf_iff_isSheaf_of_type _ _).mp (isAlgebraicSpace_yoneda B S hS V).isSheaf)
    have hPsheaf : Presheaf.IsSheaf J ((uliftYoneda.{u + 1}).obj pb) := hsheafLift pb
    have hUsheaf : Presheaf.IsSheaf J ((uliftYoneda.{u + 1}).obj (inc.obj (D_Y.obj i))) :=
      hsheafLift _
    let eP : (uliftYoneda.{u + 1}).obj pb ≅ (H.obj pb).obj := isoSheafify J hPsheaf
    let eU : (uliftYoneda.{u + 1}).obj (inc.obj (D_Y.obj i)) ≅
        (H.obj (inc.obj (D_Y.obj i))).obj := isoSheafify J hUsheaf
    have hnat : (uliftYoneda.{u + 1}).map (hRep.snd ξ) ≫ eU.hom =
        eP.hom ≫ (H.map (hRep.snd ξ)).hom := by
      change (uliftYoneda.{u + 1}).map (hRep.snd ξ) ≫
          toSheafify J ((uliftYoneda.{u + 1}).obj (inc.obj (D_Y.obj i))) =
        toSheafify J ((uliftYoneda.{u + 1}).obj pb) ≫
          sheafifyMap J ((uliftYoneda.{u + 1}).map (hRep.snd ξ))
      exact toSheafify_naturality J _
    have hnat' : (H.map (hRep.snd ξ)).hom ≫ eU.inv =
        eP.inv ≫ (uliftYoneda.{u + 1}).map (hRep.snd ξ) := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact hnat.symm
    have hsq : IsPullback (eP.hom ≫ (hRep.fst ξ).hom)
        ((uliftYoneda.{u + 1}).map (hRep.snd ξ)) f.hom (eU.hom ≫ ξ.hom) :=
      ((hRep.isPullback ξ).map (sheafToPresheaf J (Type (u + 1)))).of_iso
        eP.symm (Iso.refl _) eU.symm (Iso.refl _)
        (by
          change (sheafToPresheaf J (Type (u + 1))).map (hRep.fst ξ) ≫ 𝟙 _ =
            eP.inv ≫ eP.hom ≫ (hRep.fst ξ).hom
          rw [Category.comp_id, ← Category.assoc, eP.inv_hom_id, Category.id_comp]
          rfl)
        hnat' (by simp)
        (by
          change (sheafToPresheaf J (Type (u + 1))).map ξ ≫ 𝟙 _ = (eU.inv ≫ eU.hom) ≫ ξ.hom
          rw [Category.comp_id, eU.inv_hom_id, Category.id_comp]
          rfl)
    -- Flatness of the projection, read on the identity étale charts.
    have hflatProj : AlgebraicGeometry.Flat (T.map (hRep.snd ξ)) := by
      have h0 : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
          (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
          (pullback.fst (eU.hom ≫ ξ.hom) f.hom) :=
        hflat' (inc.obj (D_Y.obj i)) (eU.hom ≫ ξ.hom)
      have h1 := Space.holdsOnEveryEtaleChartULift_precomp B S hS
        (@AlgebraicGeometry.Flat.{u}) hsq.flip.isoPullback.hom _ h0
      rw [hsq.flip.isoPullback_hom_fst] at h1
      exact prop_of_holdsOnEveryEtaleChartULift B S hS (hRep.snd ξ) h1
    -- Surjectivity of the projection.
    have hsurjProj : AlgebraicGeometry.Surjective (T.map (hRep.snd ξ)) := by
      refine Space.surjective_of_isSurjective_yoneda_map B S hS (hRep.snd ξ) ?_
      refine (Space.isSurjectiveULift_whiskerRight_iff B S hS
        (yoneda.map (hRep.snd ξ))).mp ?_
      exact isSurjectiveULift_of_iso_comm B S hS eP eU hnat
        (IsSurjective.of_isPullback B S hS (hRep.isPullback ξ).flip hsurj)
    let : IsAffine (T.obj pb) := hpb
    let : IsAffine (T.obj (inc.obj (D_Y.obj i))) := hU
    let : AlgebraicGeometry.Flat (T.map (hRep.snd ξ)) := hflatProj
    let : AlgebraicGeometry.Surjective (T.map (hRep.snd ξ)) := hsurjProj
    have hff : RingHom.FaithfullyFlat ((T.map (hRep.snd ξ)).appTop).hom :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
        (T.map (hRep.snd ξ))).mp ⟨hflatProj, hsurjProj⟩
    obtain ⟨n, g, hg⟩ := exists_factor_to_affine_stage B S hS X ℕ D_X hD_X eX
      (⟨pb, hpb⟩ : BigAffineFppf B S hS) (hRep.fst ξ)
    exact ⟨n, H.map (inc.map g), hg, hff.injective⟩
  choose fiberIndex fiberMap hfiberMap hfiberInjective using hfiberStage
  -- The dotted arrow: every stage of `Y` factors through a member of the countable family.
  have hfactor (i : I) : ∃ n : ℕ, ∃ g : G.obj i ⟶ G.obj (targetIndex n),
      g ≫ colimit.ι G (targetIndex n) ≫ eY.inv = colimit.ι G i ≫ eY.inv := by
    let n := fiberIndex i
    let j := targetIndex n
    set ξ : G.obj i ⟶ Y := colimit.ι G i ≫ eY.inv with hξdef
    let p := hRep.snd ξ
    let b := FF.preimage (fiberMap i ≫ H.map (inc.map (targetMap n)))
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let a := inc.map (D_Y.map (homOfLE hik))
    let c := inc.map (D_Y.map (homOfLE hjk))
    have hw {x y : I} (h : x ≤ y) : H.map (inc.map (D_Y.map (homOfLE h))) ≫
        colimit.ι G y ≫ eY.inv = colimit.ι G x ≫ eY.inv := by
      change G.map (homOfLE h) ≫ colimit.ι G y ≫ eY.inv = _
      rw [colimit.w_assoc]
    have ha : H.map a ≫ colimit.ι G k ≫ eY.inv = ξ := hw hik
    have hc : H.map c ≫ colimit.ι G k ≫ eY.inv = colimit.ι G j ≫ eY.inv := hw hjk
    have hb : H.map p ≫ ξ = H.map b ≫ colimit.ι G j ≫ eY.inv := by
      rw [show H.map b = fiberMap i ≫ H.map (inc.map (targetMap n)) from FF.map_preimage _]
      rw [Category.assoc, htargetMap]
      change H.map p ≫ ξ = fiberMap i ≫ colimit.ι FX (fiberIndex i) ≫ eX.inv ≫ f
      rw [← Category.assoc _ _ f, ← Category.assoc _ _ f, hfiberMap]
      exact (hRep.isPullback ξ).w.symm
    have hcomm : p ≫ a = b ≫ c := by
      apply FF.map_injective
      let := hιmono k
      apply (cancel_mono (colimit.ι G k ≫ eY.inv)).1
      change H.map (p ≫ a) ≫ (colimit.ι G k ≫ eY.inv) =
        H.map (b ≫ c) ≫ (colimit.ι G k ≫ eY.inv)
      simp only [Functor.map_comp, Category.assoc]
      rw [ha, hc]
      exact hb
    have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion (T.map c) :=
      (hD_Y (homOfLE hjk)).1
    let : IsAffine (T.obj (inc.obj (D_Y.obj k))) := (D_Y.obj k).property
    obtain ⟨q, hq⟩ := exists_factor_over_closedImmersion_of_injective
      B S hS p a b c hclosed (hfiberInjective i) hcomm
    refine ⟨n, H.map q, ?_⟩
    change H.map q ≫ colimit.ι G j ≫ eY.inv = ξ
    rw [← hc, ← Category.assoc, ← H.map_comp, hq, ha]
  -- Monotonise the countable family and restrict the presentation to it.
  obtain ⟨seq, hseq, hle⟩ := exists_monotone_ge targetIndex
  let s := hseq.functor
  have hcover (i : I) : ∃ n, ∃ a : G.obj i ⟶ G.obj (s.obj n),
      a ≫ (colimit.cocone G).ι.app (s.obj n) = (colimit.cocone G).ι.app i := by
    obtain ⟨n, g, hg⟩ := hfactor i
    refine ⟨n, g ≫ G.map (homOfLE (hle n)), ?_⟩
    apply (cancel_mono eY.inv).1
    change (g ≫ G.map (homOfLE (hle n))) ≫ colimit.ι G (seq n) ≫ eY.inv =
      colimit.ι G i ≫ eY.inv
    simpa only [Category.assoc, colimit.w_assoc] using hg
  let hcol := isColimit_of_sequence_factors G (colimit.cocone G) (colimit.isColimit G) s
    (fun i => Sheaf.mono_colimit_ι_of_mono_transition G hGmono i) hcover
  exact ⟨s ⋙ D_Y, fun _ _ g => hD_Y (s.map g),
    ⟨eY ≪≫ hcol.coconePointUniqueUpToIso (colimit.isColimit (s ⋙ G))⟩⟩

end AlgebraicGeometry.FormalSpace

end
