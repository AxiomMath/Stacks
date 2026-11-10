module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackLimit
import all StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullback

/-!
# The pro-étale inverse image of an étale sheaf at a limit is a colimit

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale category into the small pro-étale category.  Let `Y = lim Y_i` be the
limit of a cofiltered inverse system of quasi-compact and quasi-separated objects of
`X_proétale` with affine transition morphisms.  For a sheaf `ℱ` on `X_étale`

  `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)`,

and if moreover the `Y_i` are objects of `X_étale`, then `ε⁻¹ℱ(Y) = colim ℱ(Y_i)`.  This is
Stacks 099S.  The injectivity half is
`AlgebraicGeometry.Scheme.proetaleInverseImage_exists_map_eq_of_isLimit`; this file proves the
surjectivity half and assembles the two.

## Main results

* `AlgebraicGeometry.Scheme.proetaleInverseImageIsColimit`: the formula
  `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)`: the sections of `ε⁻¹ℱ` over the stages, with their restriction
  maps to `Y`, form a colimit cocone.
* `AlgebraicGeometry.Scheme.proetaleInverseImageIsColimitOfEtale`: the formula
  `ε⁻¹ℱ(Y) = colim ℱ(Y_i)` for stages in `X_étale`, the maps `ℱ(Y_i) → ε⁻¹ℱ(Y)` being the unit
  `ℱ ⟶ ε_*ε⁻¹ℱ` followed by restriction.
* `AlgebraicGeometry.Scheme.bigEtaleInverseImage_jointly_surjective_of_isLimit`: the surjectivity
  half for the inverse image of `ℱ` on all `X`-schemes, which is the rule
  `(f : Y → X) ↦ Γ(Y_étale, f_étale⁻¹ℱ)` of Stacks 0GLZ before restriction to `X_proétale`.
* `AlgebraicGeometry.Scheme.proetaleInverseImage_jointly_surjective_of_isLimit`: the same for
  `ε⁻¹ℱ`.

## Implementation notes

By Stacks 0GLZ the sections of `ε⁻¹ℱ` at a pro-étale object are the sections, over the underlying
`X`-scheme, of the inverse image of `ℱ` on all `X`-schemes, so the formula is a statement about
that inverse image; this is the reduction of the source to Stacks 09YQ in degree zero, and the
degree-zero argument is carried out here directly.

Surjectivity: a section over `Y` is étale locally pulled back from sections of `ℱ` over étale
`X`-schemes.  By Stacks 01ZM and 07RP that étale covering of `Y` is refined by the base change of
finitely many quasi-compact schemes étale over a stage
(`AlgebraicGeometry.exists_etale_stage_of_etale_cover_of_isLimit`), and by Stacks 01ZC the
morphisms from their base changes to the étale `X`-schemes are defined at a later stage
(`AlgebraicGeometry.exists_hom_pullback_comp_eq_of_isLimit`).  At a still later stage the
resulting local sections agree on overlaps and the étale schemes cover, and the sections glue.
Here the quasi-separatedness of the stages is used, in Stacks 01ZM and 01ZC.

The local description of the sections of the big étale inverse image is the private lemma
`bigEtaleInverseImage_local_sections` of
`StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullback`, reached by `import all`.

That the limit is taken in the pro-étale site is expressed, as in the source, by asking that the
cone of underlying `X`-schemes be a limit cone of schemes; a limit of schemes of a system of
weakly étale `X`-schemes with affine transition morphisms is again weakly étale over `X`, so this
is the limit in `X_proétale`.  The index category is a small category in the universe of the
schemes, which is the generality of the limit API used, and the coefficient universe stays free.

## References

* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 0GLZ](https://stacks.math.columbia.edu/tag/0GLZ)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry

/-! ### The inverse image on all `X`-schemes -/

/-- Two composable pairs of morphisms of `Over X` with the same composite of underlying morphisms
of schemes act in the same way on a presheaf. -/
private lemma map_map_eq_of_left {X : Scheme.{u}} (P : (Over X)ᵒᵖ ⥤ Type*)
    {A B B' C : Over X} (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C)
    (h : f.left ≫ g.left = f'.left ≫ g'.left) (x : P.obj (op C)) :
    P.map f.op (P.map g.op x) = P.map f'.op (P.map g'.op x) := by
  have e : f ≫ g = f' ≫ g' := Over.OverMorphism.ext (by simpa using h)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]

/-- A composable pair of morphisms of `Over X` acts on a presheaf as a morphism with the same
underlying composite. -/
private lemma map_map_eq_map_of_left {X : Scheme.{u}} (P : (Over X)ᵒᵖ ⥤ Type*)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f.left ≫ g.left = k.left)
    (x : P.obj (op C)) : P.map f.op (P.map g.op x) = P.map k.op x := by
  have e : f ≫ g = k := Over.OverMorphism.ext (by simpa using h)
  rw [← Functor.map_comp_apply, ← op_comp, e]

/-- **Stacks 099S, the surjectivity half, for the inverse image on all `X`-schemes.** Let
`Y = lim Y_i` be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
`X`-schemes with affine transition morphisms, and let `ℱ` be a sheaf on `X_étale`.  Every section
over `Y` of the inverse image of `ℱ` on all `X`-schemes is the restriction of a section over
some stage `Y_i`.

The section is étale locally on `Y` pulled back from sections of `ℱ` over étale `X`-schemes.  By
`AlgebraicGeometry.exists_etale_stage_of_etale_cover_of_isLimit` finitely many quasi-compact
schemes `V_a` étale over a stage `Y_i` have base changes covering `Y` and refining that étale
covering, and by Stacks 01ZC (`AlgebraicGeometry.exists_hom_pullback_comp_eq_of_isLimit`) the
morphisms from those base changes to the étale `X`-schemes are defined over a later stage.  This
gives sections over the `V_a`, at a stage where the `V_a` cover; the loci where two of them agree
on overlaps are opens containing the image of the limit, so a later stage lands in them
(`AlgebraicGeometry.exists_range_pullback_snd_subset_of_isLimit`), and there the sections glue to
a section over the stage, whose restriction to `Y` is the given one. -/
public theorem Scheme.bigEtaleInverseImage_jointly_surjective_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (D : I ⥤ Over X)
    (c : Cone D) (hc : IsLimit ((Over.forget X).mapCone c))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left] [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (s : ((Scheme.bigEtaleInverseImage.{u, v} X).obj F).obj.obj (op c.pt)) :
    ∃ (i : I) (t : ((Scheme.bigEtaleInverseImage.{u, v} X).obj F).obj.obj (op (D.obj i))),
      ((Scheme.bigEtaleInverseImage.{u, v} X).obj F).obj.map (c.π.app i).op t = s := by
  classical
  let P := ((Scheme.bigEtaleInverseImage.{u, v} X).obj F).obj
  let D' : I ⥤ Scheme.{u} := D ⋙ Over.forget X
  let c' : Cone D' := (Over.forget X).mapCone c
  have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (D'.map f) := fun f =>
    inferInstanceAs (IsAffineHom (D.map f).left)
  have : ∀ a : I, CompactSpace (D'.obj a) := fun a => inferInstanceAs (CompactSpace (D.obj a).left)
  have : ∀ a : I, QuasiSeparatedSpace (D'.obj a) := fun a =>
    inferInstanceAs (QuasiSeparatedSpace (D.obj a).left)
  have hcπ : ∀ a : I, c'.π.app a ≫ (D.obj a).hom = c.pt.hom := fun a => Over.w (c.π.app a)
  have hDm : ∀ {a b : I} (f : a ⟶ b), D'.map f ≫ (D.obj b).hom = (D.obj a).hom :=
    fun f => Over.w (D.map f)
  let τ : D' ⟶ (Functor.const I).obj X :=
    { app := fun a => (D.obj a).hom
      naturality := fun a b f => (hDm f).trans (Category.comp_id _).symm }
  -- The section is étale locally pulled back from sections over étale `X`-schemes.
  obtain ⟨E, hE⟩ := bigEtaleInverseImage_local_sections.{u, v} X F c.pt s
  choose U' κ t ht using hE
  let U (k : E.I₀) : Over X := (Scheme.Etale.forget X).obj (U' k)
  have : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} :=
    Scheme.instJointlySurjectivePrecoverage (P := @Etale)
  have : ∀ k, Etale (E.f k) := fun k => E.map_prop k
  have : ∀ k, LocallyOfFinitePresentation (U k).hom := fun k =>
    have : Etale (U' k).hom := (U' k).prop
    inferInstanceAs (LocallyOfFinitePresentation (U' k).hom)
  have hκ : ∀ k, (κ k).left ≫ (U k).hom = E.f k ≫ c.pt.hom := fun k => Over.w (κ k)
  -- That étale covering is refined by the base change of finitely many étale schemes over a
  -- stage.
  obtain ⟨i, A, hA, Y, p, kk, e, hp, hYc, hYs, he, hcov⟩ :=
    exists_etale_stage_of_etale_cover_of_isLimit D' c' hc E.X E.f
      (fun x => ⟨E.idx x, E.covers x⟩)
  have : ∀ a, CompactSpace (Y a) := hYc
  have : ∀ a, QuasiSeparatedSpace (Y a) := hYs
  have : ∀ a, Etale (p a) := hp
  -- The morphisms to the étale `X`-schemes are defined over later stages.
  have hh : ∀ a, (e a ≫ (κ (kk a)).left) ≫ (U (kk a)).hom =
      pullback.fst (c'.π.app i) (p a) ≫ c'.π.app i ≫ τ.app i := by
    intro a
    change (e a ≫ (κ (kk a)).left) ≫ (U (kk a)).hom =
      pullback.fst (c'.π.app i) (p a) ≫ c'.π.app i ≫ (D.obj i).hom
    rw [Category.assoc, hκ, ← Category.assoc, he, hcπ]
  choose j f g hg₁ hg₂ using fun a => exists_hom_pullback_comp_eq_of_isLimit D' c' hc τ
    (U (kk a)).hom (p a) (e a ≫ (κ (kk a)).left) (hh a)
  -- The images of the étale schemes over the stage.
  let V₀ : (D'.obj i).Opens := ⨆ a, ⟨Set.range (p a), (p a).isOpenMap.isOpen_range⟩
  have hV₀ : ∀ y, y ∈ V₀ ↔ ∃ a, y ∈ Set.range (p a) := by
    intro y
    simp [V₀]
  obtain ⟨j₂, f₂, hf₂⟩ := exists_map_preimage_le_map_preimage D' c' hc (i := i) (U := ⊤)
    (V := V₀) (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) (by
      intro x _
      obtain ⟨a, z, rfl⟩ := hcov x
      refine (hV₀ _).2 ⟨a, pullback.snd (c'.π.app i) (p a) z, ?_⟩
      change (pullback.snd (c'.π.app i) (p a) ≫ p a) z = (pullback.fst _ _ ≫ c'.π.app i) z
      rw [pullback.condition])
  -- A common stage where the étale schemes cover and the morphisms are defined.
  obtain ⟨w₁, hw₁⟩ := common_stage_of_finite i (J := Option A)
    (fun w o => o.elim (∀ y : D'.obj w.left, D'.map w.hom y ∈ V₀)
      (fun a => Nonempty (w ⟶ Over.mk (f a))))
    (by
      rintro w w' φ (_ | a) h
      · intro y
        have := h (D'.map φ.left y)
        rwa [← Scheme.Hom.comp_apply, ← D'.map_comp, Over.w φ] at this
      · exact ⟨φ ≫ h.some⟩)
    (by
      rintro (_ | a)
      · exact ⟨Over.mk f₂, fun y => hf₂ (show y ∈ D'.map f₂ ⁻¹ᵁ ⊤ from trivial)⟩
      · exact ⟨Over.mk (f a), ⟨𝟙 _⟩⟩)
  have hw₁c : ∀ y : D'.obj w₁.left, D'.map w₁.hom y ∈ V₀ := hw₁ none
  let ψ (a : A) : w₁ ⟶ Over.mk (f a) := (hw₁ (some a)).some
  have hψ : ∀ a, (ψ a).left ≫ f a = w₁.hom := fun a => Over.w (ψ a)
  -- The sections over the étale schemes at that stage.
  let B₁ (a : A) : Over X := Over.mk (pullback.fst (D'.map w₁.hom) (p a) ≫ (D.obj w₁.left).hom)
  let tr (a : A) : pullback (D'.map w₁.hom) (p a) ⟶ pullback (D'.map (f a)) (p a) :=
    pullback.lift (pullback.fst _ _ ≫ D'.map (ψ a).left) (pullback.snd _ _)
      (by rw [Category.assoc, ← D'.map_comp, hψ]; exact pullback.condition)
  let G (a : A) : B₁ a ⟶ U (kk a) :=
    Over.homMk (tr a ≫ g a) (by
      change (tr a ≫ g a) ≫ (U (kk a)).hom = pullback.fst _ _ ≫ (D.obj w₁.left).hom
      calc (tr a ≫ g a) ≫ (U (kk a)).hom
          = tr a ≫ pullback.fst (D'.map (f a)) (p a) ≫ τ.app (j a) := by
            rw [Category.assoc, hg₂]
        _ = pullback.fst _ _ ≫ D'.map (ψ a).left ≫ (D.obj (j a)).hom := by
            rw [pullback.lift_fst_assoc, Category.assoc]
        _ = pullback.fst _ _ ≫ (D.obj w₁.left).hom :=
            congrArg (pullback.fst _ _ ≫ ·) (hDm (ψ a).left))
  let σ (a : A) : P.obj (op (B₁ a)) := P.map (G a).op (t (kk a))
  -- Restricted to the base change of the limit, they are the given section.
  let Z (a : A) : Over X := Over.mk (pullback.fst (c'.π.app i) (p a) ≫ c.pt.hom)
  let zfst (a : A) : Z a ⟶ c.pt := Over.homMk (pullback.fst _ _) rfl
  -- The base change of the limit maps to the base change of each stage.
  let Lg (a : A) (k : I) (m : k ⟶ i) :
      Z a ⟶ Over.mk (pullback.fst (D'.map m) (p a) ≫ (D.obj k).hom) :=
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ c'.π.app k) (pullback.snd _ _)
      (by rw [Category.assoc, c'.w, pullback.condition])) (by
        change _ ≫ pullback.fst _ _ ≫ _ = _
        rw [pullback.lift_fst_assoc, Category.assoc, hcπ]
        rfl)
  let L (a : A) : Z a ⟶ B₁ a := Lg a w₁.left w₁.hom
  have key : ∀ a, P.map (L a).op (σ a) = P.map (zfst a).op s := by
    intro a
    let e' : Z a ⟶ Over.mk (E.f (kk a) ≫ c.pt.hom) :=
      Over.homMk (e a) (by
        change e a ≫ E.f (kk a) ≫ c.pt.hom = _
        rw [← Category.assoc, he]
        rfl)
    refine (map_map_eq_of_left P (L a) (G a) e' (κ (kk a)) ?_ (t (kk a))).trans ?_
    · change pullback.lift _ _ _ ≫ tr a ≫ g a = e a ≫ (κ (kk a)).left
      rw [← hg₁ a, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · simp only [tr, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [c'.w]
      · simp only [tr, Category.assoc, pullback.lift_snd]
    · rw [ht]
      refine map_map_eq_map_of_left P e' _ (zfst a) ?_ s
      exact he a
  -- The stages are quasi-compact.
  have hB₁c : ∀ a, CompactSpace (B₁ a).left := fun a =>
    inferInstanceAs (CompactSpace ↑(pullback (D'.map w₁.hom) (p a)))
  -- The overlaps at that stage, and the loci where the two sections agree on them.
  let T (q : A × A) : Scheme.{u} :=
    pullback (pullback.fst (D'.map w₁.hom) (p q.1)) (pullback.fst (D'.map w₁.hom) (p q.2))
  let rT (q : A × A) : T q ⟶ D'.obj w₁.left := pullback.fst _ _ ≫ pullback.fst _ _
  have hTc : ∀ q, CompactSpace (T q) := fun q => by
    have : CompactSpace (B₁ q.2).left := hB₁c q.2
    exact inferInstanceAs (CompactSpace (T q))
  let To (q : A × A) : Over X := Over.mk (rT q ≫ (D.obj w₁.left).hom)
  let T₁ (q : A × A) : To q ⟶ B₁ q.1 :=
    Over.homMk (pullback.fst _ _) (Category.assoc _ _ _).symm
  let T₂ (q : A × A) : To q ⟶ B₁ q.2 :=
    Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ pullback.fst _ _ ≫ _ = (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _
      rw [← pullback.condition_assoc, Category.assoc])
  choose W hW using fun q : A × A => Scheme.bigEtaleInverseImage_openEq_over.{u, v} X F (To q)
    (P.map (T₁ q).op (σ q.1)) (P.map (T₂ q).op (σ q.2))
  -- Over the limit the two sections agree on the overlaps.
  have hlim : ∀ q : A × A,
      Set.range (pullback.snd (c'.π.app w₁.left) (rT q)) ⊆ (W q : Set (To q).left) := by
    intro q
    let Xq : Over X := Over.mk (pullback.snd (c'.π.app w₁.left) (rT q) ≫ (To q).hom)
    let gq : Xq ⟶ To q := Over.homMk (pullback.snd _ _) rfl
    have hXq : pullback.fst (c'.π.app w₁.left) (rT q) ≫ c.pt.hom = Xq.hom := by
      change _ = pullback.snd _ _ ≫ rT q ≫ (D.obj w₁.left).hom
      rw [← pullback.condition_assoc, hcπ]
    let fq : Xq ⟶ c.pt := Over.homMk (pullback.fst _ _) hXq
    have side : ∀ (b : A) (Tb : To q ⟶ B₁ b) (_ : Tb.left ≫ pullback.fst _ _ = rT q),
        P.map gq.op (P.map Tb.op (σ b)) = P.map fq.op s := by
      intro b Tb hTb
      let M : Xq ⟶ Z b := Over.homMk
        (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Tb.left ≫ pullback.snd _ _) (by
          rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc Tb.left,
            hTb, ← pullback.condition_assoc, c'.w]))
        (by
          change _ ≫ pullback.fst _ _ ≫ c.pt.hom = _
          rw [pullback.lift_fst_assoc, hXq])
      refine (map_map_eq_of_left P gq Tb M (L b) ?_ (σ b)).trans ?_
      · change pullback.snd _ _ ≫ Tb.left = M.left ≫ pullback.lift _ _ _
        apply pullback.hom_ext
        · simp only [M, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hTb,
            Over.homMk_left]
          exact pullback.condition.symm
        · simp only [M, Over.homMk_left, Category.assoc, pullback.lift_snd]
      · rw [key]
        exact map_map_eq_map_of_left P M (zfst b) fq (pullback.lift_fst _ _ _) s
    simpa [gq] using (hW q Xq gq).mp
      ((side q.1 (T₁ q) rfl).trans (side q.2 (T₂ q) pullback.condition.symm).symm)
  -- Hence at a later stage.
  obtain ⟨v, hv⟩ := common_stage_of_finite w₁.left (J := A × A)
    (fun v q => Set.range (pullback.snd (D'.map v.hom) (rT q)) ⊆ (W q : Set (To q).left))
    (by
      intro v v' φ q h
      refine (range_pullback_snd_subset_of_fac _ _ (D'.map φ.left) ?_ (rT q)).trans h
      rw [← D'.map_comp, Over.w φ])
    (fun q => by
      have := hTc q
      obtain ⟨j', f', h'⟩ := exists_range_pullback_snd_subset_of_isLimit D' c' hc (rT q) (W q)
        (hlim q)
      exact ⟨Over.mk f', h'⟩)
  -- The final stage, and the étale covering of it.
  let jf : I := v.left
  let ρ : jf ⟶ i := v.hom ≫ w₁.hom
  let Bf (a : A) : Over X := Over.mk (pullback.fst (D'.map ρ) (p a) ≫ (D.obj jf).hom)
  let bf (a : A) : Bf a ⟶ D.obj jf := Over.homMk (pullback.fst _ _) rfl
  let trf (a : A) : Bf a ⟶ B₁ a := Over.homMk
    (pullback.lift (pullback.fst _ _ ≫ D'.map v.hom) (pullback.snd _ _)
      (by rw [Category.assoc, ← D'.map_comp]; exact pullback.condition))
    (by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = pullback.fst _ _ ≫ _
      rw [pullback.lift_fst_assoc, Category.assoc, hDm])
  let σf (a : A) : P.obj (op (Bf a)) := P.map (trf a).op (σ a)
  have hcompat : Presieve.Arrows.Compatible P bf σf := by
    intro a a' Zc l l' hll'
    have hll : l.left ≫ pullback.fst _ _ = l'.left ≫ pullback.fst _ _ :=
      congrArg (fun m => m.left) hll'
    let q : A × A := (a, a')
    have hcond : (l.left ≫ (trf a).left) ≫ pullback.fst (D'.map w₁.hom) (p a) =
        (l'.left ≫ (trf a').left) ≫ pullback.fst (D'.map w₁.hom) (p a') := by
      simp only [trf, Category.assoc, Over.homMk_left, pullback.lift_fst]
      rw [reassoc_of% hll]
    let m : Zc.left ⟶ T q := pullback.lift (l.left ≫ (trf a).left) (l'.left ≫ (trf a').left)
      hcond
    have hm₁ : m ≫ pullback.fst _ _ = l.left ≫ (trf a).left := pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd _ _ = l'.left ≫ (trf a').left := pullback.lift_snd _ _ _
    let mo : Zc ⟶ To q := Over.homMk m (by
      change m ≫ (pullback.fst _ _ ≫ pullback.fst _ _) ≫ _ = Zc.hom
      rw [Category.assoc, ← Category.assoc m, hm₁]
      exact Over.w (l ≫ trf a))
    have hm : Set.range m ⊆ (W q : Set (To q).left) := by
      refine Set.Subset.trans ?_ (hv q)
      rintro _ ⟨z, rfl⟩
      refine ⟨pullback.lift (l.left ≫ pullback.fst _ _) m ?_ z, ?_⟩
      · change _ = m ≫ pullback.fst _ _ ≫ pullback.fst _ _
        rw [← Category.assoc m, hm₁]
        simp only [Category.assoc]
        exact congrArg (l.left ≫ ·) (pullback.lift_fst _ _ _).symm
      · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    change P.map l.op (P.map (trf a).op (σ a)) = P.map l'.op (P.map (trf a').op (σ a'))
    rw [map_map_eq_of_left P l (trf a) mo (T₁ q) hm₁.symm, (hW q Zc mo).mpr hm,
      map_map_eq_of_left P mo (T₂ q) l' (trf a') hm₂]
  have hcov' : Sieve.ofArrows Bf bf ∈ (Scheme.etaleTopology.over X) (D.obj jf) := by
    rw [GrothendieckTopology.mem_over_iff]
    let Q : Presieve (D.obj jf).left :=
      Presieve.ofArrows (fun a => (Bf a).left) (fun a => (bf a).left)
    have hQ : Q ∈ Scheme.etalePrecoverage (D.obj jf).left := by
      constructor
      · rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
        intro y
        obtain ⟨a, ha⟩ := (hV₀ _).1 (hw₁c (D'.map v.hom y))
        refine ⟨_, _, Presieve.ofArrows.mk a, ?_⟩
        change y ∈ Set.range (pullback.fst (D'.map ρ) (p a))
        have h2 : ∀ y' : D'.obj jf, D'.map ρ y' = D'.map w₁.hom (D'.map v.hom y') := fun y' => by
          rw [← Scheme.Hom.comp_apply, ← D'.map_comp]
        rw [Scheme.Pullback.range_fst]
        exact (show D'.map ρ y ∈ Set.range (p a) from (h2 y).symm ▸ ha)
      · rintro _ _ ⟨a⟩
        change Etale (pullback.fst (D'.map ρ) (p a))
        exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    exact (Scheme.etaleTopology).superset_covering
      ((Sieve.generate_le_iff _ _).mpr (by
        rintro _ _ ⟨a⟩
        rw [Sieve.overEquiv_iff]
        exact Sieve.ofArrows_mk _ _ a))
      (Precoverage.generate_mem_toGrothendieck hQ)
  -- The sections glue over the final stage.
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Scheme.bigEtaleInverseImage.{u, v} X).obj F).property
  have H : Presieve.IsSheafFor P (Presieve.ofArrows Bf bf) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (hsh.isSheafFor _ (by rwa [Sieve.generate_sieve]))
  obtain ⟨tf, htf, -⟩ := (Presieve.isSheafFor_arrows_iff P bf).mp H σf hcompat
  -- The glued section restricts to the given one over the limit.
  refine ⟨jf, tf, ?_⟩
  obtain ⟨W₀, hW₀⟩ := Scheme.bigEtaleInverseImage_openEq_over.{u, v} X F c.pt
    (P.map (c.π.app jf).op tf) s
  have hall : Set.range (𝟙 c.pt : c.pt ⟶ c.pt).left ⊆ W₀ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, y, hy⟩ := (hV₀ _).1 (hw₁c (c'.π.app w₁.left x))
    rw [← Scheme.Hom.comp_apply, c'.w] at hy
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    let Lf : Z a ⟶ Bf a := Lg a jf ρ
    have hagree : P.map (zfst a).op (P.map (c.π.app jf).op tf) = P.map (zfst a).op s := by
      rw [map_map_eq_of_left P (zfst a) (c.π.app jf) Lf (bf a) (pullback.lift_fst _ _ _).symm,
        htf a]
      refine (map_map_eq_map_of_left P Lf (trf a) (L a) ?_ (σ a)).trans (key a)
      change pullback.lift _ _ _ ≫ pullback.lift _ _ _ = pullback.lift _ _ _
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [c'.w]
      · simp only [Category.assoc, pullback.lift_snd]
    simpa using (hW₀ (Z a) (zfst a)).mp hagree ⟨z, hz⟩
  simpa using (hW₀ c.pt (𝟙 c.pt)).mpr hall

/-! ### The pro-étale inverse image -/

section ProEt

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.ProEt)
  (c : Cone Y) (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
  (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))

include hc

/-- **Surjectivity, for the formula of Stacks 0GLZ.** For a cofiltered inverse system of
quasi-compact and quasi-separated pro-étale objects with affine transitions whose underlying
schemes have limit `Y`, every section over `Y` of the rule `(f : Y → X) ↦ Γ(Y_étale, f_étale⁻¹ℱ)`
is the restriction of a section over some stage. -/
public theorem Scheme.etaleSectionsSheaf_jointly_surjective_of_isLimit
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (s : ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.obj (op c.pt)) :
    ∃ (i : I) (t : ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.obj (op (Y.obj i))),
      ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.map (c.π.app i).op t = s := by
  let D : I ⥤ Over X := Y ⋙ Scheme.ProEt.forget X
  have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (D.map f).left := fun f =>
    inferInstanceAs (IsAffineHom (Y.map f).left)
  have : ∀ a : I, CompactSpace (D.obj a).left := fun a =>
    inferInstanceAs (CompactSpace (Y.obj a).left)
  have : ∀ a : I, QuasiSeparatedSpace (D.obj a).left := fun a =>
    inferInstanceAs (QuasiSeparatedSpace (Y.obj a).left)
  exact Scheme.bigEtaleInverseImage_jointly_surjective_of_isLimit.{u, v} X D
    ((Scheme.ProEt.forget X).mapCone c) hc F s

/-- The sections of `ε⁻¹ℱ` are those of the rule of Stacks 0GLZ. -/
private abbrev proetaleInverseImageObjIso :
    ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj ≅
      ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj :=
  (sheafToPresheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))).mapIso
    ((Scheme.proetaleInverseImageIsoEtaleSectionsSheaf.{u, v} X).app F)

/-- **Stacks 099S, surjectivity.** Let `Y = lim Y_i` be the limit of a cofiltered inverse system
of quasi-compact and quasi-separated objects of `X_proétale` with affine transition morphisms, and
let `ℱ` be a sheaf on `X_étale`.  Every section of `ε⁻¹ℱ` over `Y` is the restriction of a
section over some stage `Y_i`. -/
public theorem Scheme.proetaleInverseImage_jointly_surjective_of_isLimit
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (s : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology
      (Scheme.ProEt.topology X)).obj F).obj.obj (op c.pt)) :
    ∃ (i : I) (t : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).obj F).obj.obj (op (Y.obj i))),
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).obj F).obj.map (c.π.app i).op t = s := by
  let e := proetaleInverseImageObjIso.{u, v} X F
  obtain ⟨i, t, ht⟩ := Scheme.etaleSectionsSheaf_jointly_surjective_of_isLimit.{u, v} X Y c hc F
    (e.hom.app _ s)
  refine ⟨i, e.inv.app _ t,
    (ConcreteCategory.bijective_of_isIso (e.hom.app (op c.pt))).injective ?_⟩
  rwa [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply]

end ProEt

/-- **Stacks 099S.** Let `X` be a scheme, let `Y = lim Y_i` be the limit of a cofiltered inverse
system of quasi-compact and quasi-separated objects of `X_proétale` with affine transition
morphisms, and let `ℱ` be a sheaf on `X_étale`.  Then `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)`: the sections
of `ε⁻¹ℱ` over the stages, with their restriction maps to `Y`, form a colimit cocone. -/
public def Scheme.proetaleInverseImageIsColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.ProEt)
    (c : Cone Y) (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) :
    IsColimit (((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.mapCocone
        c.op) := by
  let G := ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj
  refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_)
  · obtain ⟨i, t, ht⟩ := Scheme.proetaleInverseImage_jointly_surjective_of_isLimit.{u, v} X Y c
      hc F x
    exact ⟨op i, t, ht.symm⟩
  · let k : I := IsCofiltered.min i.unop j.unop
    let fi : k ⟶ i.unop := IsCofiltered.minToLeft i.unop j.unop
    let fj : k ⟶ j.unop := IsCofiltered.minToRight i.unop j.unop
    have hk : G.map (c.π.app k).op (G.map (Y.map fi).op xi) =
        G.map (c.π.app k).op (G.map (Y.map fj).op xj) := by
      rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        ← op_comp, c.w, c.w]
    obtain ⟨l, g, hlg⟩ := Scheme.proetaleInverseImage_exists_map_eq_of_isLimit.{u, v} X Y c hc
      (fun f => inferInstance) (fun i => inferInstance) F k _ _ hk
    refine ⟨op l, (g ≫ fi).op, (g ≫ fj).op, ?_⟩
    change G.map (Y.map (g ≫ fi)).op xi = G.map (Y.map (g ≫ fj)).op xj
    rwa [Y.map_comp, Y.map_comp, op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]

/-- **Stacks 099S, the final statement.** If, in the situation of
`AlgebraicGeometry.Scheme.proetaleInverseImageIsColimit`, the stages `Y_i` are objects of
`X_étale`, then `ε⁻¹ℱ(Y) = colim ℱ(Y_i)`: the sections of `ℱ` over the stages, mapped to
`ε⁻¹ℱ(Y)` by the unit `ℱ ⟶ ε_*ε⁻¹ℱ` followed by restriction, form a colimit cocone.

The unit is an isomorphism by Stacks 099T, which reduces this to the displayed formula. -/
public def Scheme.proetaleInverseImageIsColimitOfEtale
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.Etale)
    (c : Cone (Y ⋙ X.etaleToProetale))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) :
    IsColimit ((Cocone.precompose (Functor.whiskerLeft Y.op
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F).hom)).obj
      (((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.mapCocone
          c.op)) := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((Y ⋙ X.etaleToProetale).map f).left :=
    fun f => inferInstanceAs (IsAffineHom (Y.map f).left)
  have : ∀ i : I, CompactSpace ((Y ⋙ X.etaleToProetale).obj i).left :=
    fun i => inferInstanceAs (CompactSpace (Y.obj i).left)
  have : ∀ i : I, QuasiSeparatedSpace ((Y ⋙ X.etaleToProetale).obj i).left :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Y.obj i).left)
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} X
  have : IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F).hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf X.smallEtaleTopology (Type (max (u + 1) v))).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F)))
  exact (IsColimit.precomposeHomEquiv (asIso (Functor.whiskerLeft Y.op
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F).hom))
    _).symm (Scheme.proetaleInverseImageIsColimit.{u, v} X (Y ⋙ X.etaleToProetale) c hc F)

end AlgebraicGeometry

end
