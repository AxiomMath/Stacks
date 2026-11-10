module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.EqualityLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.LocalAgreement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Shrink
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.Glue
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.SectionEqualityLocus

/-!
# Agreement of pulled-back sections at a point

Let `F` be a sheaf on the small étale site of a scheme `X` and let `s j` be sections of `F` over
objects `W j` of that site. A morphism of schemes `G : Q ⟶ W j` over `X`, from an arbitrary
scheme `Q`, should be thought of as a way of pulling `s j` back to `Q`; it is not a morphism of
the site, as `Q` need not be étale over `X`. Two such morphisms `G : Q ⟶ W j` and
`G' : Q ⟶ W j'` combine to `Q ⟶ W j ×_X W j'`, and the two pulled-back sections **agree at a
point `q` of `Q`** when the image of `q` in `W j ×_X W j'` lies in the open locus where
`s j` and `s j'` agree (`Stacks.EtaleCohomology.smallEtaleEqLocusUnconditional`).

This is the form in which the surjectivity half of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) compares sections on a scheme
finite over `X`: there the sections live on the inverse image of `F`, and their agreement near a
point is exactly agreement in the present sense. Phrasing it through the pair `W j ×_X W j'`
makes it a statement about one point of one scheme, and avoids the inverse image altogether.

Agreement at a point is an equivalence relation on such morphisms (reflexivity is the diagonal,
symmetry the swap, transitivity the triple fibre product), it is pulled back along morphisms into
`Q`, and the points where it holds form an open subset. The last result is the local input of
Tag 09ZF: if the `s j` all pull back to the same section of `i^{-1}F` along a morphism
`i : Z ⟶ X`, then any two of them agree at every point of `Q` lying over the image of `i`.

## Main definitions

* `Stacks.EtaleCohomology.pairEqLocus` — the open of `W j ×_X W j'` where `s j` and `s j'` agree.
* `Stacks.EtaleCohomology.pairLift` — the morphism `Q ⟶ W j ×_X W j'` of two morphisms over `X`.
* `Stacks.EtaleCohomology.PairAgree` — agreement of two pulled-back sections at a point.

## Main results

* `Stacks.EtaleCohomology.pairAgree_comp_iff` — agreement is pulled back along morphisms.
* `Stacks.EtaleCohomology.isOpen_setOf_pairAgree` — the agreement locus is open.
* `Stacks.EtaleCohomology.pairAgree_refl`, `PairAgree.symm`, `PairAgree.trans` — it is an
  equivalence relation.
* `Stacks.EtaleCohomology.mem_smallEtaleEqLocus_of_sectionPullback_eq` — two sections with the
  same pullback along `i` agree near every point over the image of `i`.
* `Stacks.EtaleCohomology.pairAgree_of_mem_range` — sections cutting out the same global
  section of `i^{-1}F` agree at every point over the image of `i`.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v w

namespace Stacks.EtaleCohomology

section Agreement

variable {X : Scheme.{u}} (F : Sheaf (Scheme.smallEtaleTopology X) (Type w))
  {α : Type*} (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j)))

/-- Restricting twice is restricting along the composite. -/
public theorem map_map_apply {V V' V'' : X.Etale} (f : V' ⟶ V) (g : V'' ⟶ V')
    (a : F.obj.obj (op V)) :
    F.obj.map g.op (F.obj.map f.op a) = F.obj.map (g ≫ f).op a := by
  rw [op_comp, F.obj.map_comp, types_comp_apply]

/-- The open of `W j ×_X W j'` over which `s j` and `s j'` agree. -/
public def pairEqLocus (j j' : α) : (smallEtalePair (W j) (W j')).left.Opens :=
  smallEtaleEqLocusUnconditional F (F.obj.map (smallEtalePairFst (W j) (W j')).op (s j))
    (F.obj.map (smallEtalePairSnd (W j) (W j')).op (s j'))

/-- The morphism into `W j ×_X W j'` determined by two morphisms over `X`. -/
public def pairLift {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left) (G' : Q ⟶ (W j').left)
    (hG : G ≫ ((W j).hom : (W j).left ⟶ X) = G' ≫ ((W j').hom : (W j').left ⟶ X)) :
    Q ⟶ (smallEtalePair (W j) (W j')).left :=
  pullback.lift G G' hG

/-- The first projection of `pairLift W G G' hG` is `G`. -/
@[reassoc (attr := simp)]
public theorem pairLift_fst {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left)
    (G' : Q ⟶ (W j').left) (hG) :
    pairLift W G G' hG ≫ (smallEtalePairFst (W j) (W j')).left = G :=
  pullback.lift_fst _ _ _

/-- The second projection of `pairLift W G G' hG` is `G'`. -/
@[reassoc (attr := simp)]
public theorem pairLift_snd {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left)
    (G' : Q ⟶ (W j').left) (hG) :
    pairLift W G G' hG ≫ (smallEtalePairSnd (W j) (W j')).left = G' :=
  pullback.lift_snd _ _ _

/-- Two morphisms into `W j ×_X W j'` are equal when their projections are. -/
public theorem smallEtalePair_hom_ext {Q : Scheme.{u}} {j j' : α}
    {a b : Q ⟶ (smallEtalePair (W j) (W j')).left}
    (h₁ : a ≫ (smallEtalePairFst (W j) (W j')).left = b ≫ (smallEtalePairFst (W j) (W j')).left)
    (h₂ : a ≫ (smallEtalePairSnd (W j) (W j')).left = b ≫ (smallEtalePairSnd (W j) (W j')).left) :
    a = b :=
  pullback.hom_ext h₁ h₂

/-- The first component of the morphism `Y ⟶ W ×_X V` of the site given by two morphisms. -/
@[reassoc (attr := simp)]
public theorem smallEtalePairLift_left_fst {W' V' Y : X.Etale} (g₁ : Y ⟶ W') (g₂ : Y ⟶ V') :
    (smallEtalePairLift g₁ g₂).left ≫ (smallEtalePairFst W' V').left = g₁.left :=
  pullback.lift_fst _ _ _

/-- The second component of the morphism `Y ⟶ W ×_X V` of the site given by two morphisms. -/
@[reassoc (attr := simp)]
public theorem smallEtalePairLift_left_snd {W' V' Y : X.Etale} (g₁ : Y ⟶ W') (g₂ : Y ⟶ V') :
    (smallEtalePairLift g₁ g₂).left ≫ (smallEtalePairSnd W' V').left = g₂.left :=
  pullback.lift_snd _ _ _

/-- Two pulled-back sections **agree at the point `q`** of `Q` when the image of `q` in
`W j ×_X W j'` lies in the locus where `s j` and `s j'` agree. -/
public def PairAgree {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left) (G' : Q ⟶ (W j').left)
    (hG : G ≫ ((W j).hom : (W j).left ⟶ X) = G' ≫ ((W j').hom : (W j').left ⟶ X)) (q : Q) :
    Prop :=
  (pairLift W G G' hG).base q ∈ pairEqLocus F W s j j'

variable {F W s}

/-- The pair morphism of two composites is the composite of the pair morphism. -/
public theorem comp_pairLift {Q Q' : Scheme.{u}} (ψ : Q' ⟶ Q) {j j' : α}
    (G : Q ⟶ (W j).left) (G' : Q ⟶ (W j').left) (hG) (hG') :
    pairLift W (ψ ≫ G) (ψ ≫ G') hG' = ψ ≫ pairLift W G G' hG :=
  smallEtalePair_hom_ext W (by simp) (by simp)

/-- **Agreement is pulled back.** Two pulled-back sections agree at `q'` after composing with
`ψ : Q' ⟶ Q` exactly when they agree at `ψ q'`. -/
public theorem pairAgree_comp_iff {Q Q' : Scheme.{u}} (ψ : Q' ⟶ Q) {j j' : α}
    {G : Q ⟶ (W j).left} {G' : Q ⟶ (W j').left} (hG) (hG') (q' : Q') :
    PairAgree F W s (ψ ≫ G) (ψ ≫ G') hG' q' ↔ PairAgree F W s G G' hG (ψ.base q') := by
  unfold PairAgree
  rw [comp_pairLift ψ G G' hG hG', Scheme.Hom.comp_apply]

/-- A variant of `Stacks.EtaleCohomology.pairAgree_comp_iff` for morphisms which are only known
to factor through `ψ`. -/
public theorem pairAgree_of_comp {Q Q' : Scheme.{u}} (ψ : Q' ⟶ Q) {j j' : α}
    {G : Q ⟶ (W j).left} {G' : Q ⟶ (W j').left} {H : Q' ⟶ (W j).left} {H' : Q' ⟶ (W j').left}
    (hG) (hH) (e : ψ ≫ G = H) (e' : ψ ≫ G' = H') {q' : Q'} {q : Q} (hq : ψ.base q' = q) :
    PairAgree F W s G G' hG q → PairAgree F W s H H' hH q' := by
  subst e e' hq
  exact (pairAgree_comp_iff ψ hG hH q').2

/-- The converse of `Stacks.EtaleCohomology.pairAgree_of_comp`. -/
public theorem pairAgree_of_comp' {Q Q' : Scheme.{u}} (ψ : Q' ⟶ Q) {j j' : α}
    {G : Q ⟶ (W j).left} {G' : Q ⟶ (W j').left} {H : Q' ⟶ (W j).left} {H' : Q' ⟶ (W j').left}
    (hG) (hH) (e : ψ ≫ G = H) (e' : ψ ≫ G' = H') {q' : Q'} {q : Q} (hq : ψ.base q' = q) :
    PairAgree F W s H H' hH q' → PairAgree F W s G G' hG q := by
  subst e e' hq
  exact (pairAgree_comp_iff ψ hG hH q').1

/-- **The agreement locus is open**: it is the preimage of an open under a continuous map. -/
public theorem isOpen_setOf_pairAgree {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left)
    (G' : Q ⟶ (W j').left) (hG) :
    IsOpen {q | PairAgree F W s G G' hG q} :=
  (pairEqLocus F W s j j').isOpen.preimage (pairLift W G G' hG).continuous

/-- **Reflexivity**: a pulled-back section agrees with itself, the image of a point lying on the
diagonal, along which the two projections agree. -/
public theorem pairAgree_refl {Q : Scheme.{u}} {j : α} (G : Q ⟶ (W j).left) (q : Q) :
    PairAgree F W s G G rfl q := by
  have hΔ : pairLift W G G rfl =
      G ≫ (smallEtalePairLift (𝟙 (W j)) (𝟙 (W j))).left :=
    smallEtalePair_hom_ext W
      (by
        rw [pairLift_fst, Category.assoc, smallEtalePairLift_left_fst]
        exact (Category.comp_id G).symm)
      (by
        rw [pairLift_snd, Category.assoc, smallEtalePairLift_left_snd]
        exact (Category.comp_id G).symm)
  unfold PairAgree
  rw [hΔ, Scheme.Hom.comp_apply]
  refine range_subset_smallEtaleEqLocus_general (smallEtalePairLift (𝟙 (W j)) (𝟙 (W j))) ?_ ⟨_, rfl⟩
  rw [map_map_apply, map_map_apply, smallEtalePairLift_fst, smallEtalePairLift_snd]

/-- The image of a point of the locus where two sections agree, under a morphism of the site,
lies in the locus where their restrictions agree: membership form of
`Stacks.EtaleCohomology.preimage_smallEtaleEqLocus`. -/
public theorem mem_smallEtaleEqLocus_map_iff {V V' : X.Etale} (h : V' ⟶ V)
    (a b : F.obj.obj (op V)) (x : V'.left) :
    h.left.base x ∈ smallEtaleEqLocusUnconditional F a b ↔
      x ∈ smallEtaleEqLocusUnconditional F (F.obj.map h.op a) (F.obj.map h.op b) := by
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← preimage_smallEtaleEqLocus]
  rfl

/-- Membership in `pairEqLocus` of the image under a morphism `f` of the site into `W j ×_X W j'`
is membership in the equality locus of the two restrictions along `f`. -/
private theorem comp_mem_pairEqLocus_iff {j j' : α} {T : X.Etale}
    (f : T ⟶ smallEtalePair (W j) (W j')) (x : T.left) :
    f.left.base x ∈ pairEqLocus F W s j j' ↔
      x ∈ smallEtaleEqLocusUnconditional F (F.obj.map (f ≫ smallEtalePairFst (W j) (W j')).op (s j))
        (F.obj.map (f ≫ smallEtalePairSnd (W j) (W j')).op (s j')) := by
  unfold pairEqLocus
  rw [mem_smallEtaleEqLocus_map_iff, map_map_apply, map_map_apply]

/-- **Symmetry**, through the swap of the two factors of `W j ×_X W j'`. -/
public theorem PairAgree.symm {Q : Scheme.{u}} {j j' : α} {G : Q ⟶ (W j).left}
    {G' : Q ⟶ (W j').left} {hG} {q : Q} (h : PairAgree F W s G G' hG q) :
    PairAgree F W s G' G hG.symm q := by
  have hσ : pairLift W G' G hG.symm ≫
      (smallEtalePairLift (smallEtalePairSnd (W j') (W j)) (smallEtalePairFst (W j') (W j))).left
        = pairLift W G G' hG :=
    smallEtalePair_hom_ext W
      (by rw [Category.assoc, smallEtalePairLift_left_fst, pairLift_snd, pairLift_fst])
      (by rw [Category.assoc, smallEtalePairLift_left_snd, pairLift_fst, pairLift_snd])
  unfold PairAgree at h ⊢
  rw [← hσ, Scheme.Hom.comp_apply, comp_mem_pairEqLocus_iff] at h
  unfold pairEqLocus
  rw [smallEtaleEqLocus_comm]
  simpa using h

/-- **Transitivity**, through the triple fibre product `(W j₁ ×_X W j₂) ×_X W j₃`: the image of
`q` there lies in the loci where `s j₁, s j₂` and where `s j₂, s j₃` agree, hence in the locus
where `s j₁, s j₃` agree. -/
public theorem PairAgree.trans {Q : Scheme.{u}} {j₁ j₂ j₃ : α} {G₁ : Q ⟶ (W j₁).left}
    {G₂ : Q ⟶ (W j₂).left} {G₃ : Q ⟶ (W j₃).left} {h₁₂ h₂₃} (h₁₃) {q : Q}
    (a : PairAgree F W s G₁ G₂ h₁₂ q) (b : PairAgree F W s G₂ G₃ h₂₃ q) :
    PairAgree F W s G₁ G₃ h₁₃ q := by
  let P := smallEtalePair (W j₁) (W j₂)
  let T := smallEtalePair P (W j₃)
  let π₁₂ : T ⟶ P := smallEtalePairFst P (W j₃)
  let π₂₃ : T ⟶ smallEtalePair (W j₂) (W j₃) :=
    smallEtalePairLift (π₁₂ ≫ smallEtalePairSnd _ _) (smallEtalePairSnd P (W j₃))
  let π₁₃ : T ⟶ smallEtalePair (W j₁) (W j₃) :=
    smallEtalePairLift (π₁₂ ≫ smallEtalePairFst _ _) (smallEtalePairSnd P (W j₃))
  have hτ : pairLift W G₁ G₂ h₁₂ ≫ ((P.hom : P.left ⟶ X)) =
      G₃ ≫ ((W j₃).hom : (W j₃).left ⟶ X) := by
    change pairLift W G₁ G₂ h₁₂ ≫ (smallEtalePairFst (W j₁) (W j₂)).left ≫
      ((W j₁).hom : (W j₁).left ⟶ X) = _
    rw [pairLift_fst_assoc, h₁₃]
  let τ : Q ⟶ T.left := pullback.lift (pairLift W G₁ G₂ h₁₂) G₃ hτ
  have e₁₂ : τ ≫ π₁₂.left = pairLift W G₁ G₂ h₁₂ := pullback.lift_fst _ _ _
  have e₃ : τ ≫ (smallEtalePairSnd P (W j₃)).left = G₃ := pullback.lift_snd _ _ _
  have e₂₃ : τ ≫ π₂₃.left = pairLift W G₂ G₃ h₂₃ :=
    smallEtalePair_hom_ext W
      (by
        rw [Category.assoc, smallEtalePairLift_left_fst, pairLift_fst]
        change (τ ≫ π₁₂.left) ≫ (smallEtalePairSnd (W j₁) (W j₂)).left = G₂
        rw [e₁₂, pairLift_snd])
      (by rw [Category.assoc, smallEtalePairLift_left_snd, e₃, pairLift_snd])
  have e₁₃ : τ ≫ π₁₃.left = pairLift W G₁ G₃ h₁₃ :=
    smallEtalePair_hom_ext W
      (by
        rw [Category.assoc, smallEtalePairLift_left_fst, pairLift_fst]
        change (τ ≫ π₁₂.left) ≫ (smallEtalePairFst (W j₁) (W j₂)).left = G₁
        rw [e₁₂, pairLift_fst])
      (by rw [Category.assoc, smallEtalePairLift_left_snd, e₃, pairLift_snd])
  unfold PairAgree at a b ⊢
  rw [← e₁₂, Scheme.Hom.comp_apply, comp_mem_pairEqLocus_iff] at a
  rw [← e₂₃, Scheme.Hom.comp_apply, comp_mem_pairEqLocus_iff,
    smallEtalePairLift_fst, smallEtalePairLift_snd] at b
  rw [← e₁₃, Scheme.Hom.comp_apply, comp_mem_pairEqLocus_iff,
    smallEtalePairLift_fst, smallEtalePairLift_snd]
  exact smallEtaleEqLocus_trans _ _ _ ⟨a, b⟩

end Agreement

section Pullback

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
  (F : Sheaf (Scheme.smallEtaleTopology X) (Type (max (u + 1) v)))

/-- **Sections with the same pullback agree near the image.** If two sections `a b` of `F` over
an object `V` of the small étale site of `X` have the same pullback to `V ×_X Z` along
`i : Z ⟶ X`, then every point of `V` over the image of `i` lies in their equality locus.

The pullbacks agree in the sheafification of the left Kan extension, so they agree in the Kan
extension itself on a covering family of `V ×_X Z`; one of its members reaches the given point,
and there equality in the Kan extension is witnessed by a morphism `V' ⟶ V` of the site through
which that member factors, by
`_root_.Stacks.EtaleCohomology.exists_map_eq_of_lan_eq`. -/
public theorem mem_smallEtaleEqLocus_of_sectionPullback_eq {V : X.Etale}
    {a b : F.obj.obj (op V)}
    (hab : smallEtaleSectionPullback.{u, v} i F V a = smallEtaleSectionPullback.{u, v} i F V b)
    (x : V.left) (hx : (V.hom : V.left ⟶ X).base x ∈ Set.range i.base) :
    x ∈ smallEtaleEqLocusUnconditional F a b := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨ζ, hζ₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
  have hR : Presheaf.equalizerSieve
      (F := (smallEtaleBaseChange i).op.lan.obj F.obj)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) a)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) b) ∈
      Scheme.smallEtaleTopology Z ((smallEtaleBaseChange i).obj V) :=
    equalizerSieve_mem_of_toSheafify_eq _ _ _ hab
  obtain ⟨β, Y, p, hEq⟩ := (Presheaf.equalizerSieve
      (F := (smallEtaleBaseChange i).op.lan.obj F.obj)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) a)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) b)).exists_eq_ofArrows
  have hcov : ⋃ m, Set.range (p m).left = Set.univ :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp (hEq ▸ hR)
  obtain ⟨m, y, hy⟩ : ∃ m, ζ ∈ Set.range (p m).left :=
    Set.mem_iUnion.mp (hcov ▸ Set.mem_univ ζ)
  have hmem : (Presheaf.equalizerSieve
      (F := (smallEtaleBaseChange i).op.lan.obj F.obj)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) a)
      (((smallEtaleBaseChange i).op.lanUnit.app F.obj).app (op V) b)).arrows (p m) := by
    rw [hEq]
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨m, 𝟙 _, (Category.id_comp _).symm⟩
  obtain ⟨V', q, k', hk', hq⟩ :=
    _root_.Stacks.EtaleCohomology.exists_map_eq_of_lan_eq i (p m) F a b hmem
  refine range_subset_smallEtaleEqLocus_general q hq ⟨(pullback.fst (V'.hom : V'.left ⟶ X) i).base
    (k'.left.base y), ?_⟩
  rw [← hζ₁, ← hy]
  have h1 : k'.left ≫ ((smallEtaleBaseChange i).map q).left ≫
      pullback.fst (V.hom : V.left ⟶ X) i =
      k'.left ≫ pullback.fst (V'.hom : V'.left ⟶ X) i ≫ q.left := by
    rw [map_smallEtaleBaseChange_left_fst]
    rfl
  have h2 : (p m).left ≫ pullback.fst (V.hom : V.left ⟶ X) i =
      k'.left ≫ pullback.fst (V'.hom : V'.left ⟶ X) i ≫ q.left := by
    rw [← hk']
    exact (Category.assoc _ _ _).trans h1
  have h3 := congrArg (fun f ↦ f.base y) h2
  simp only [Scheme.Hom.comp_apply] at h3
  exact h3.symm

variable {α : Type*} (W : α → X.Etale) (s : ∀ j, F.obj.obj (op (W j)))
  (t : ((smallEtaleInverseImage.{u, v} i).obj F).obj.obj (op (terminal Z.Etale)))

/-- **Sections presenting the same global section of `i^{-1}F` agree over the image of `i`.**
If the pullback of each `s j` to `W j ×_X Z` is the restriction of one global section `t` of
`i^{-1}F`, then any two of the sections, pulled back to a scheme `Q` along morphisms
`G : Q ⟶ W j` and `G' : Q ⟶ W j'` over `X`, agree at every point of `Q` lying over the image of
`i`.

The restrictions of `s j` and `s j'` to `W j ×_X W j'` both pull back to the restriction of `t`,
so `Stacks.EtaleCohomology.mem_smallEtaleEqLocus_of_sectionPullback_eq` applies at the image of
the point. -/
public theorem pairAgree_of_mem_range
    (ht : ∀ j, ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
          (terminal.from ((smallEtaleBaseChange i).obj (W j))).op t
        = smallEtaleSectionPullback.{u, v} i F (W j) (s j))
    {Q : Scheme.{u}} {j j' : α} (G : Q ⟶ (W j).left) (G' : Q ⟶ (W j').left) (hG) (q : Q)
    (hq : (G ≫ ((W j).hom : (W j).left ⟶ X)).base q ∈ Set.range i.base) :
    PairAgree F W s G G' hG q := by
  have key : ∀ (j₀ : α) (f : smallEtalePair (W j) (W j') ⟶ W j₀),
      smallEtaleSectionPullback.{u, v} i F _ (F.obj.map f.op (s j₀)) =
        ((smallEtaleInverseImage.{u, v} i).obj F).obj.map
          (terminal.from ((smallEtaleBaseChange i).obj (smallEtalePair (W j) (W j')))).op t := by
    intro j₀ f
    rw [← smallEtaleSectionPullback_map.{u, v} i F f (s j₀), ← ht j₀,
      ← CategoryTheory.Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim ((smallEtaleBaseChange i).map f ≫
        terminal.from ((smallEtaleBaseChange i).obj (W j₀)))
        (terminal.from ((smallEtaleBaseChange i).obj (smallEtalePair (W j) (W j'))))]
  refine mem_smallEtaleEqLocus_of_sectionPullback_eq.{u, v} i F
    ((key j _).trans (key j' _).symm) _ ?_
  change ((pairLift W G G' hG ≫ (smallEtalePairFst (W j) (W j')).left) ≫
    ((W j).hom : (W j).left ⟶ X)).base q ∈ _
  rwa [pairLift_fst]

end Pullback

end Stacks.EtaleCohomology

end
