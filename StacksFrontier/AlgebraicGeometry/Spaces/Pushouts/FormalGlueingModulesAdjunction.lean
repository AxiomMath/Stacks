module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# The adjunction of formal glueing of quasi-coherent modules

In the formal glueing situation `f : Y ⟶ X`, `Z ⊆ X` of Stacks 0AEV, the functor of Stacks 0AEW
sending a quasi-coherent `𝒪_X`-module `M` to the triple `(M|_U, f^*M, can)` is left adjoint to the
functor of Stacks 0AEX sending a triple `(H, G, φ)` to `Ker(j_*H ⊕ f_*G ⟶ (f ∘ j')_*(G|_V))`.
This file proves the inputs of Stacks 0AEY; the adjunction itself, with no hypothesis, is
`AlgebraicGeometry.Space.FormalGlueingSituation.glueingAdjunction` in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional`.

## Main definitions

* `CategoryTheory.Functor.whiskerLeftToCommaIso`: whiskering a functor into a comma category
  built by `CategoryTheory.Functor.toComma` on the left.
* `CategoryTheory.Adjunction.toCommaPullbackAdjunction`: **the abstract adjunction**, between a
  functor `CategoryTheory.Functor.toComma F G α` into a comma category and a functor which,
  together with two transformations to the two direct images, is the pullback of the two
  transposed legs; and `CategoryTheory.Adjunction.toCommaPullbackAdjunctionRestrict`, the same
  restricted along two fully faithful inclusions.
* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapPullbackCompIso`: the comparison
  `(f|_V)^* ∘ j^* ≅ (f ∘ j')^*` of inverse images along the two legs of the glueing square.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelFst` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelSnd`: the two projections of the
  module of Stacks 0AEX onto `j_*H` and onto `f_*G`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_app_comp`: transposing along two adjunctions turns
  precomposition with a transformation of left adjoints into postcomposition with its mate.
* `CategoryTheory.Adjunction.homEquiv_left_leg` and
  `CategoryTheory.Adjunction.homEquiv_right_leg`: **the two mate computations**, which say that the
  two canonical maps of Stacks 0AEX are the transposes of the two legs of the commutative square
  carried by a morphism of glueing triples.
* `CategoryTheory.Limits.isPullback_kernel_ι_biprod`: in a preadditive category the kernel of a
  map out of a binary biproduct restricting to `r` and to `-s` on the two summands is the
  pullback of `r` and `s`.
* `AlgebraicGeometry.Space.conjugateEquiv_eqToHom_modulePullback`: the mate of the transport of
  inverse images along an equality of morphisms is the transport of direct images.
* `AlgebraicGeometry.Space.FormalGlueingSituation.conjugateEquiv_overlapPullbackCompIso_inv` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.conjugateEquiv_modulePullbackCompIso_overlap_inv`:
  the comparisons of inverse images along the two legs of the glueing square are the mates of the
  comparisons of direct images along them.  These are the two inputs the mate computations need.
* `AlgebraicGeometry.Space.FormalGlueingSituation.inr_comp_glueingKernelMap`: the map of
  Stacks 0AEX restricts to the negative of the second canonical map on the summand `f_*G`; the
  companion of
  `AlgebraicGeometry.Space.FormalGlueingSituation.inl_comp_glueingKernelMap`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel`: the module of
  Stacks 0AEX, with its two projections, is the pullback of the two canonical maps.

## Implementation notes

**The adjunction is a term, with its unit and counit, and not an existence statement.**  It is
produced by `CategoryTheory.Adjunction.mkOfHomEquiv` from the natural bijection of hom-sets, so
every map obtained by transposing along it is a named morphism.

**All of the mathematics is proved over abstract categories.**  A morphism of glueing triples
`(M|_U, f^*M, can) ⟶ (H, G, φ)` is a pair of a map `j^*M ⟶ H` and a map `f^*M ⟶ G` making the
square over the overlap `V` commute.  Transposing the first along `j^* ⊣ j_*` and the second along
`f^* ⊣ f_*` gives a pair of maps `M ⟶ j_*H` and `M ⟶ f_*G`; the content of Stacks 0AEY is that
the commuting square becomes exactly the condition that the two composites into
`(f ∘ j')_*(G|_V)` agree, so that the pair is a map into the kernel of Stacks 0AEX.  The two
halves of that translation are `CategoryTheory.Adjunction.homEquiv_left_leg` and
`CategoryTheory.Adjunction.homEquiv_right_leg`: each says that one of the two canonical maps of
Stacks 0AEX is a mate, and each is proved from `CategoryTheory.conjugateEquiv` and the
compatibility of the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU with the comparison
`f_* ∘ g_* ≅ (f ≫ g)_*`, which is
`AlgebraicGeometry.Space.modulePullbackCompIso_eq_leftAdjointCompIso`.

This is the discipline the two files for Stacks 0AEW and Stacks 0AEX record, and here it is
forced rather than chosen.  At the concrete categories of modules the three operations that
reduce a term are each, on their own, out of reach:

* **Whole-functor identities.**  `rfl` on
  `ambientInclusion ⋙ glueingDiagram = quasicoherentGlueingDiagram`, an identity that holds
  definitionally, exhausts the heartbeat budget, and so does `rfl` on either of its two
  components at an object.  Every identification below is therefore stated in the shape that an
  abstract lemma, or an existing `rfl` lemma, delivers it in; in particular the two commutation
  identities of the restriction are identities between the two spellings the existing files
  already use, and `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionOverlapMap_eq` and
  its companion state the two canonical maps of Stacks 0AEX as whiskered composites rather than
  pointwise, because the pointwise form is the one that does not reduce.
* **Reduction inside a concrete functor.**  `(F.whiskerRight α).app t = F.map (α.app t)` is
  `CategoryTheory.Functor.whiskerRight_app`, but `F.map ((G.whiskerLeft β).app t) =
  F.map (β.app (G.obj t))` — the same reduction performed *inside* `F.map` — does not terminate.
  That is why the abstract adjunction takes the two canonical maps as whiskered composites and
  does the pointwise computation itself, over abstract categories.
* **Re-synthesised additive structure.**  The identity
  `biprod.inr ≫ glueingKernelMap = -ambientOverlapMap`, an instance of
  `CategoryTheory.Limits.biprod.inr_desc`, cannot be checked by the kernel at the functor
  category over the `𝒪_X`-modules — the implementation notes of the file for Stacks 0AEX record
  the same measurement.  It *can* be checked one glueing triple at a time, which is what
  `AlgebraicGeometry.Space.FormalGlueingSituation.inr_comp_glueingKernelMap` does: `ext` first,
  then the instance.

The abstract adjunction accordingly takes the right adjoint as a functor `K` together with two
natural transformations to the two direct images forming a pullback square
(`CategoryTheory.Adjunction.toCommaPullbackAdjunction`), rather than as a literal kernel.  That
keeps the biproduct and kernel instances out of the abstract argument, and the kernel of
Stacks 0AEX is fitted to it by
`AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel`.  The abstract
argument needs the square objectwise, and gets it from the square of natural transformations
along evaluation, which preserves pullbacks because limits in a functor category are computed
objectwise.

The restriction to the quasi-coherent modules and to the glueing data of Stacks 0AEW is
`CategoryTheory.Adjunction.restrictFullyFaithful` along the two inclusions of full subcategories;
the two commutation isomorphisms are identities, because both functors of the restricted
adjunction are `CategoryTheory.ObjectProperty.lift`s of the two ambient ones.

## References

* [Stacks Project, Tag 0AEY](https://stacks.math.columbia.edu/tag/0AEY)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Functor

section WhiskerToComma

variable {A : Type u₁} [Category.{v₁} A] {Bb : Type u₂} [Category.{v₂} Bb]
    {T : Type u₃} [Category.{v₃} T] {E : Type u₄} [Category.{v₄} E]
    {E' : Type u₅} [Category.{v₅} E']

/-- Reassociated whiskering of `toComma`. -/
def whiskerLeftToCommaIso {L : A ⥤ T} {R : Bb ⥤ T} (H : E' ⥤ E) (F : E ⥤ A) (G : E ⥤ Bb)
    (α : F ⋙ L ⟶ G ⋙ R) (α' : (H ⋙ F) ⋙ L ⟶ (H ⋙ G) ⋙ R)
    (h : ∀ X, α'.app X = α.app (H.obj X)) :
    H ⋙ toComma F G α ≅ toComma (H ⋙ F) (H ⋙ G) α' :=
  NatIso.ofComponents (fun X => Comma.isoMk (Iso.refl _) (Iso.refl _) (by simp [h]))
    (fun f => by ext <;> simp [Comma.isoMk])

end WhiskerToComma

end Functor

namespace Limits

section KernelPullback

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- In a preadditive category the kernel of a map out of a binary biproduct which restricts to
`r` on the first summand and to `-s` on the second is the pullback of `r` and `s`: a section of
it is a pair of sections whose two composites agree. -/
theorem isPullback_kernel_ι_biprod {X Y Z : C} [HasBinaryBiproduct X Y] (g : X ⊞ Y ⟶ Z)
    [HasKernel g] {r : X ⟶ Z} {s : Y ⟶ Z}
    (hl : biprod.inl ≫ g = r) (hr : biprod.inr ≫ g = -s) :
    IsPullback (kernel.ι g ≫ biprod.fst) (kernel.ι g ≫ biprod.snd) r s := by
  have hg : g = biprod.desc (biprod.inl ≫ g) (biprod.inr ≫ g) := by
    apply biprod.hom_ext' <;> simp
  have hd : ∀ {W : C} (p : W ⟶ X ⊞ Y),
      p ≫ g = (p ≫ biprod.fst) ≫ r - (p ≫ biprod.snd) ≫ s := by
    intro W p
    have hp : p = biprod.lift (p ≫ biprod.fst) (p ≫ biprod.snd) := by
      apply biprod.hom_ext <;> simp
    calc p ≫ g = biprod.lift (p ≫ biprod.fst) (p ≫ biprod.snd) ≫ g := by rw [← hp]
      _ = biprod.lift (p ≫ biprod.fst) (p ≫ biprod.snd) ≫
            biprod.desc (biprod.inl ≫ g) (biprod.inr ≫ g) := by
          rw [← hg]
      _ = (p ≫ biprod.fst) ≫ (biprod.inl ≫ g) +
            (p ≫ biprod.snd) ≫ (biprod.inr ≫ g) := biprod.lift_desc
      _ = (p ≫ biprod.fst) ≫ r - (p ≫ biprod.snd) ≫ s := by
          rw [hl, hr]
          simp [sub_eq_add_neg]
  refine IsPullback.mk' ?_ ?_ ?_
  · have h0 := kernel.condition g
    rw [hd] at h0
    exact sub_eq_zero.mp h0
  · intro T φ φ' h₁ h₂
    refine (cancel_mono (kernel.ι g)).1 (biprod.hom_ext _ _ ?_ ?_)
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc] using h₂
  · intro T a b w
    refine ⟨kernel.lift g (biprod.lift a b) ?_, ?_, ?_⟩
    · rw [hd]
      simp [w]
    · rw [← Category.assoc, kernel.lift_ι]
      simp
    · rw [← Category.assoc, kernel.lift_ι]
      simp

end KernelPullback

end Limits

namespace Adjunction

section HomEquivConjugate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Transposing along two adjunctions, precomposition with a transformation of left adjoints
becomes postcomposition with its conjugate. -/
theorem homEquiv_app_comp {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : L₂ ⟶ L₁) (X : C) (Y : D) (h : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (β.app X ≫ h) =
      adj₁.homEquiv X Y h ≫ (conjugateEquiv adj₁ adj₂ β).app Y := by
  have hu := unit_conjugateEquiv adj₁ adj₂ β X
  have hn := (conjugateEquiv adj₁ adj₂ β).naturality h
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc, ← Category.assoc, hu]

end HomEquivConjugate

section CommaPullback

variable {E : Type u₁} [Category.{v₁} E] {A : Type u₂} [Category.{v₂} A]
    {Bb : Type u₃} [Category.{v₃} Bb] {T : Type u₄} [Category.{v₄} T]
    {F : E ⥤ A} {F' : A ⥤ E} {G : E ⥤ Bb} {G' : Bb ⥤ E}
    {L : A ⥤ T} {L' : T ⥤ A} {R : Bb ⥤ T} {R' : T ⥤ Bb} {N : E ⥤ T} {N' : T ⥤ E}

/-- The transpose of the left leg of a glueing triple. -/
theorem homEquiv_left_leg (adjF : F ⊣ F') (adjL : L ⊣ L') (adjN : N ⊣ N')
    (cF : F ⋙ L ≅ N) (pF : L' ⋙ F' ⟶ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pF)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : ∀ t : Comma L R, r.app t =
      F'.map (adjL.unit.app t.left) ≫ pF.app (L.obj t.left) ≫ N'.map t.hom)
    (M : E) (t : Comma L R) (a : M ⟶ F'.obj t.left) :
    adjN.homEquiv M (R.obj t.right)
        (cF.inv.app M ≫ L.map ((adjF.homEquiv M t.left).symm a) ≫ t.hom) = a ≫ r.app t := by
  rw [homEquiv_app_comp (adjF.comp adjL) adjN cF.inv, hpF, comp_homEquiv]
  rw [hr]
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit (adj := adjL),
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hn := pF.naturality t.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]

/-- The transpose of the right leg of a glueing triple. -/
theorem homEquiv_right_leg (adjG : G ⊣ G') (adjR : R ⊣ R') (adjN : N ⊣ N')
    (cG : G ⋙ R ≅ N) (pG : R' ⋙ G' ⟶ N')
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG)
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hs : ∀ t : Comma L R, s.app t =
      G'.map (adjR.unit.app t.right) ≫ pG.app (R.obj t.right))
    (M : E) (t : Comma L R) (b : M ⟶ G'.obj t.right) :
    adjN.homEquiv M (R.obj t.right)
        (cG.inv.app M ≫ R.map ((adjG.homEquiv M t.right).symm b)) = b ≫ s.app t := by
  rw [homEquiv_app_comp (adjG.comp adjR) adjN cG.inv, hpG, comp_homEquiv, hs]
  simp only [Equiv.trans_apply]
  rw [show R.map ((adjG.homEquiv M t.right).symm b) =
      R.map ((adjG.homEquiv M t.right).symm b) ≫ 𝟙 _ by simp,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit (adj := adjR),
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp

/-- **The adjunction.** -/
noncomputable def toCommaPullbackAdjunction [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G') (adjL : L ⊣ L')
    (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    {α : F ⋙ L ⟶ G ⋙ R} (hα : ∀ M, α.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s) :
    Functor.toComma F G α ⊣ K := by
  have hK : ∀ t : Comma L R, IsPullback (κ₁.app t) (κ₂.app t) (r.app t) (s.app t) := fun t =>
    Functor.map_isPullback ((evaluation (Comma L R) E).obj t) hKnat
  have hr' : ∀ t : Comma L R, r.app t = F'.map (adjL.unit.app t.left) ≫
      (pFmid.hom ≫ eN).app (L.obj t.left) ≫ N'.map t.hom := by
    intro t
    rw [hr]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Comma.natTrans_app, Functor.comp_obj, Comma.fst_obj, Comma.snd_obj, Category.assoc]
    rw [eN.naturality t.hom]
  have hs' : ∀ t : Comma L R, s.app t =
      G'.map (adjR.unit.app t.right) ≫ pG.hom.app (R.obj t.right) := by
    intro t
    rw [hs]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Comma.snd_obj]
  have hleft : ∀ (M : E) (t : Comma L R) (u : F.obj M ⟶ t.left),
      adjF.homEquiv M t.left u ≫ r.app t =
        adjN.homEquiv M (R.obj t.right) (cF.inv.app M ≫ L.map u ≫ t.hom) := by
    intro M t u
    rw [← homEquiv_left_leg adjF adjL adjN cF (pFmid.hom ≫ eN) hpF hr' M t
      (adjF.homEquiv M t.left u), Equiv.symm_apply_apply]
  have hright : ∀ (M : E) (t : Comma L R) (v : G.obj M ⟶ t.right),
      adjG.homEquiv M t.right v ≫ s.app t =
        adjN.homEquiv M (R.obj t.right) (cF.inv.app M ≫ α.app M ≫ R.map v) := by
    intro M t v
    rw [← homEquiv_right_leg adjG adjR adjN cG pG.hom hpG hs' M t (adjG.homEquiv M t.right v),
      Equiv.symm_apply_apply]
    congr 1
    rw [hα]
    simp
  have key : ∀ (M : E) (t : Comma L R) (u : F.obj M ⟶ t.left) (v : G.obj M ⟶ t.right),
      (L.map u ≫ t.hom = α.app M ≫ R.map v) ↔
        (adjF.homEquiv M t.left u ≫ r.app t = adjG.homEquiv M t.right v ≫ s.app t) := by
    intro M t u v
    rw [hleft, hright]
    have : IsIso (cF.inv.app M) := ⟨cF.hom.app M, by simp, by simp⟩
    constructor
    · intro h; rw [h]
    · intro h
      exact (cancel_epi (cF.inv.app M)).1 ((adjN.homEquiv M (R.obj t.right)).injective h)
  exact Adjunction.mkOfHomEquiv
    { homEquiv := fun M t =>
        { toFun := fun g => (hK t).lift (adjF.homEquiv M t.left g.left)
            (adjG.homEquiv M t.right g.right) ((key M t g.left g.right).1 g.w)
          invFun := fun k =>
            { left := (adjF.homEquiv M t.left).symm (k ≫ κ₁.app t)
              right := (adjG.homEquiv M t.right).symm (k ≫ κ₂.app t)
              w := by
                refine (key M t _ _).2 ?_
                rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.assoc,
                  Category.assoc, (hK t).w] }
          left_inv := fun g => by
            refine Comma.hom_ext _ _ ?_ ?_
            · dsimp only
              rw [(hK t).lift_fst]
              exact Equiv.symm_apply_apply _ _
            · dsimp only
              rw [(hK t).lift_snd]
              exact Equiv.symm_apply_apply _ _
          right_inv := fun k => by
            dsimp only
            refine (hK t).hom_ext ?_ ?_
            · rw [(hK t).lift_fst, Equiv.apply_symm_apply]
            · rw [(hK t).lift_snd, Equiv.apply_symm_apply] }
      homEquiv_naturality_left_symm := fun {M' M t} f k => by
        refine Comma.hom_ext _ _ ?_ ?_
        · change (adjF.homEquiv M' t.left).symm ((f ≫ k) ≫ κ₁.app t) =
            F.map f ≫ (adjF.homEquiv M t.left).symm (k ≫ κ₁.app t)
          rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm]
        · change (adjG.homEquiv M' t.right).symm ((f ≫ k) ≫ κ₂.app t) =
            G.map f ≫ (adjG.homEquiv M t.right).symm (k ≫ κ₂.app t)
          rw [Category.assoc, Adjunction.homEquiv_naturality_left_symm]
      homEquiv_naturality_right := fun {M t t'} g q => by
        dsimp only [Equiv.coe_fn_mk]
        refine (hK t').hom_ext ?_ ?_
        · rw [(hK t').lift_fst, Category.assoc, κ₁.naturality q, ← Category.assoc,
            (hK t).lift_fst]
          exact Adjunction.homEquiv_naturality_right (adj := adjF) g.left q.left
        · rw [(hK t').lift_snd, Category.assoc, κ₂.naturality q, ← Category.assoc,
            (hK t).lift_snd]
          exact Adjunction.homEquiv_naturality_right (adj := adjG) g.right q.right }

/-- The adjunction, restricted along two fully faithful inclusions. -/
noncomputable def toCommaPullbackAdjunctionRestrict [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G')
    (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R)
    (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s)
    {E₀ : Type*} [Category* E₀] {iE : E₀ ⥤ E} (ffE : iE.FullyFaithful)
    {Q : Type*} [Category* Q] {iQ : Q ⥤ Comma L R} (ffQ : iQ.FullyFaithful)
    {Lq : E₀ ⥤ Q} {Rq : Q ⥤ E₀}
    (cq : (iE ⋙ F) ⋙ L ≅ (iE ⋙ G) ⋙ R) (hcq : cq = Functor.isoWhiskerLeft iE αIso)
    (comm₁ : Lq ⋙ iQ = Functor.toComma (iE ⋙ F) (iE ⋙ G) cq.hom)
    (comm₂ : iQ ⋙ K = Rq ⋙ iE) :
    Lq ⊣ Rq :=
  (toCommaPullbackAdjunction adjF adjG adjL adjR adjN cF cG pFmid eN pG hpF hpG hα hr hs
    hKnat).restrictFullyFaithful ffE ffQ
      (Functor.whiskerLeftToCommaIso iE F G αIso.hom cq.hom
        (fun X => by rw [hcq]; simp) ≪≫ eqToIso comm₁.symm) (eqToIso comm₂)

end CommaPullback

end Adjunction

end CategoryTheory


universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The mate of the transport of inverse images along an equality of morphisms is the transport of
direct images along the same equality. -/
theorem conjugateEquiv_eqToHom_modulePullback {X Y : AlgebraicSpaces B S hS} {p q : X ⟶ Y}
    (h : p = q) :
    conjugateEquiv (modulePullbackAdjunction B S hS p) (modulePullbackAdjunction B S hS q)
        (eqToHom (congrArg (fun g : X ⟶ Y => modulePullback B S hS g) h).symm) =
      eqToHom (congrArg (fun g : X ⟶ Y => modulePushforward B S hS g) h) := by
  cases h
  simp

/-- The mate of the comparison of inverse images along a composite is the comparison of direct
images along it. -/
private theorem conjugateEquiv_modulePullbackCompIso_inv_aux {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((modulePullbackAdjunction B S hS g).comp (modulePullbackAdjunction B S hS f))
        (modulePullbackAdjunction B S hS (f ≫ g)) (modulePullbackCompIso B S hS f g).inv =
      (modulePushforwardCompIso B S hS f g).hom := by
  rw [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

namespace FormalGlueingSituation

variable (D : FormalGlueingSituation B S hS)

/-! ### The two legs of the glueing square as comparisons with `f ∘ j'` -/

/-- The comparison `(f|_V)^* ∘ j^* ≅ (f ∘ j')^*` of inverse images along the two legs of the
glueing square: the comparison of Stacks 03LU for `j ∘ f|_V`, transported along the commutativity
of the square. -/
def overlapPullbackCompIso :
    modulePullback B S hS D.openImmersion ⋙ modulePullback B S hS D.overlapRestriction ≅
      modulePullback B S hS (D.openImmersionOver ≫ D.ambientMorphism) :=
  modulePullbackCompIso B S hS D.overlapRestriction D.openImmersion ≪≫
    eqToIso (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePullback B S hS g)
      D.overlapRestriction_comp_openImmersion)

/-- **The comparison along the first leg is a mate.**  The comparison of inverse images along
`j ∘ f|_V` is the mate of the comparison of direct images along it, transported the same way.
This is `AlgebraicGeometry.Space.modulePullbackCompIso_eq_leftAdjointCompIso` composed with
`AlgebraicGeometry.Space.conjugateEquiv_eqToHom_modulePullback`. -/
theorem conjugateEquiv_overlapPullbackCompIso_inv :
    conjugateEquiv ((modulePullbackAdjunction B S hS D.openImmersion).comp
          (modulePullbackAdjunction B S hS D.overlapRestriction))
        (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
        D.overlapPullbackCompIso.inv =
      (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom ≫
        eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
          D.overlapRestriction_comp_openImmersion) := by
  have h₂ := conjugateEquiv_eqToHom_modulePullback (B := B) (S := S) (hS := hS)
    D.overlapRestriction_comp_openImmersion
  rw [overlapPullbackCompIso, Iso.trans_inv, eqToIso.inv,
    ← conjugateEquiv_comp ((modulePullbackAdjunction B S hS D.openImmersion).comp
      (modulePullbackAdjunction B S hS D.overlapRestriction))
      (modulePullbackAdjunction B S hS (D.overlapRestriction ≫ D.openImmersion))
      (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism)),
    conjugateEquiv_modulePullbackCompIso_inv_aux D.overlapRestriction D.openImmersion, h₂]

/-- **The comparison along the second leg is a mate.**  The comparison of inverse images along
`f ∘ j'` is the mate of the comparison of direct images along it. -/
theorem conjugateEquiv_modulePullbackCompIso_overlap_inv :
    conjugateEquiv ((modulePullbackAdjunction B S hS D.ambientMorphism).comp
          (modulePullbackAdjunction B S hS D.openImmersionOver))
        (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
        (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism).inv =
      (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism).hom :=
  conjugateEquiv_modulePullbackCompIso_inv_aux D.openImmersionOver D.ambientMorphism

/-- The overlap comparison of Stacks 0AEW, factored through the inverse image along `f ∘ j'`. -/
theorem overlapPullbackComparison_hom_app
    (M : Modules.{u, u} B S hS D.spaceX.1 D.spaceX.2) :
    D.overlapPullbackComparison.hom.app M =
      D.overlapPullbackCompIso.hom.app M ≫
        (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism).inv.app M :=
  (Category.assoc _ _ _).symm

/-- The overlap comparison of Stacks 0AEW on the quasi-coherent modules is the whiskering of the
one on all modules. -/
theorem quasicoherentOverlapComparison_eq :
    D.quasicoherentOverlapComparison =
      Functor.isoWhiskerLeft D.ambientInclusion D.overlapPullbackComparison :=
  rfl

/-! ### The two canonical maps of Stacks 0AEX -/

/-- The first canonical map of Stacks 0AEX, written out: the direct image along `j` of the unit of
`(f|_V)^* ⊣ (f|_V)_*`, the comparison of direct images, the structure arrow of the triple, and the
transport along the commutativity of the glueing square. -/
theorem restrictionOverlapMap_eq :
    D.restrictionOverlapMap =
      Functor.whiskerRight (Functor.whiskerLeft
          (Comma.fst (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver))
          (modulePullbackAdjunction B S hS D.overlapRestriction).unit)
          (modulePushforward B S hS D.openImmersion) ≫
        Functor.whiskerLeft (Comma.fst (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.overlapRestriction)
          (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion).hom ≫
        Functor.whiskerRight (Comma.natTrans (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver))
          (modulePushforward B S hS (D.overlapRestriction ≫ D.openImmersion)) ≫
        Functor.whiskerLeft (Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.openImmersionOver)
          (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
            D.overlapRestriction_comp_openImmersion)) :=
  rfl

/-- The second canonical map of Stacks 0AEX, written out: the direct image along `f` of the unit
of `(j')^* ⊣ (j')_*` followed by the comparison of direct images. -/
theorem ambientOverlapMap_eq :
    D.ambientOverlapMap =
      Functor.whiskerRight (Functor.whiskerLeft
          (Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver))
          (modulePullbackAdjunction B S hS D.openImmersionOver).unit)
          (modulePushforward B S hS D.ambientMorphism) ≫
        Functor.whiskerLeft (Comma.snd (modulePullback B S hS D.overlapRestriction)
            (modulePullback B S hS D.openImmersionOver) ⋙
            modulePullback B S hS D.openImmersionOver)
          (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism).hom :=
  rfl

/-! ### The module of Stacks 0AEX as a pullback -/

/-- The projection of the module of Stacks 0AEX onto the summand `j_*H`. -/
def glueingKernelFst : D.glueingKernelDiagram ⟶ D.restrictionDirectImage :=
  kernel.ι D.glueingKernelMap ≫ biprod.fst

/-- The projection of the module of Stacks 0AEX onto the summand `f_*G`. -/
def glueingKernelSnd : D.glueingKernelDiagram ⟶ D.ambientDirectImage :=
  kernel.ι D.glueingKernelMap ≫ biprod.snd

/-- The map of Stacks 0AEX restricts to the negative of the second canonical map on the summand
`f_*G`; the companion of `AlgebraicGeometry.Space.FormalGlueingSituation.inl_comp_glueingKernelMap`.

It is proved objectwise, which is what makes it feasible: the identity of natural
transformations is an instance of `CategoryTheory.Limits.biprod.inr_desc`, but reducing that
instance at the functor category over the `𝒪_X`-modules exhausts the kernel, whereas reducing it
at each glueing triple does not — see the implementation notes. -/
theorem inr_comp_glueingKernelMap :
    biprod.inr ≫ D.glueingKernelMap = -D.ambientOverlapMap := by
  ext t
  simp only [glueingKernelMap, biprod.inr_desc]

/-- **The module of Stacks 0AEX is a pullback.**  The kernel of the difference of the two
canonical maps, with its two projections, is the pullback of those maps: a section of it is a
pair of a section of `j_*H` and a section of `f_*G` agreeing on the overlap. -/
theorem isPullback_glueingKernel :
    IsPullback D.glueingKernelFst D.glueingKernelSnd D.restrictionOverlapMap
      D.ambientOverlapMap :=
  isPullback_kernel_ι_biprod D.glueingKernelMap D.inl_comp_glueingKernelMap
    D.inr_comp_glueingKernelMap

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
