module

public import StacksFrontier.AlgebraicGeometry.F6Rank147.ContractionUniversalProperty
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChangeGeneric
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# The stratification for base change of scheme-theoretic images

Let `S` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` a morphism of schemes over
`S` with both `X` and `Y` of finite presentation over `S`. Stacks 0H41 produces a finite chain of
closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` such that each `S_i → S` is defined by a finite
type ideal sheaf, `S₀ ⊆ S` is a thickening, and formation of the scheme-theoretic image of the
base change of `f` to each stratum `S_i ∖ S_{i+1}` commutes with arbitrary base change.

The proof is the one in the Stacks text: descend the whole situation to a Noetherian base using
absolute Noetherian approximation (Stacks 07RN) and the descent of a finitely presented morphism
(Stacks 01ZM), where every quasi-coherent ideal sheaf is automatically of finite type; there run
Noetherian induction on the base, starting from its reduction and removing at each step the
nonempty open over which compatibility with base change is known generically
(`Stacks.GenericFlatness.exists_good_open_of_isReduced`); and finally pull the resulting chain
back to `S`, which keeps the finite type condition by
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.comap`.

## Main definitions

* `AlgebraicGeometry.HasImageBaseChangeStratification` is the conclusion of Stacks 0H41 for one
  morphism over `S`.
* `Stacks.GenericFlatness.HasStratification` is the same shape of conclusion with the condition
  imposed on the strata left as a parameter.

## Main results

* `AlgebraicGeometry.hasImageBaseChangeStratification`: Stacks 0H41.
* `Stacks.GenericFlatness.exists_stratification_of_isNoetherian`: the Noetherian induction.
* `Stacks.GenericFlatness.HasStratification.comap`: a stratification pulls back along any
  morphism of bases, provided the condition on the strata is stable under precomposition.

## Implementation notes

The chain of closed subschemes is recorded exactly as in
`AlgebraicGeometry.HasFlatStratification`, the conclusion of Stacks 0H3Z: a descending chain of
closed subschemes of `S` is the *ascending* chain `I : Fin (t + 1) → S.IdealSheafData` of their
quasi-coherent ideal sheaves, `S_t = ∅` is `I (Fin.last t) = ⊤`, the finite type condition is
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, the thickening condition is
`Stacks.Thickenings.IsThickening` of `(I 0).subschemeι`, and the locally closed stratum
`S_i ∖ S_{i+1}` is the open subscheme `(I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl`
of `S_i`. The two statements are therefore directly comparable.

The Noetherian induction is run on `TopologicalSpace.Closeds S` with
`Stacks.GenericFlatness.exists_finite_descending_chain`, not with
`Stacks.GenericFlatness.exists_strata`: the latter records only that the chain of closed sets is
antitone and reaches `⊥`, whereas the stratum condition here has to be verified at every step
before the last, which needs each earlier closed set to be nonempty — that is, the chain has to be
strictly descending.

## References

* [Stacks Project, Tag 0H41](https://stacks.math.columbia.edu/tag/0H41)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.GenericFlatness

/-! ### The shape of the conclusion -/

/-- **The shape of the conclusion of Stacks 0H41 and of Stacks 0H3Z.** There is a finite
descending chain of closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of `S`, recorded by the
ascending chain `I` of their quasi-coherent ideal sheaves, such that each `S_i → S` is defined by
a finite type ideal sheaf, `S₀ ⊆ S` is a thickening, and the condition `P` holds for each stratum
`S_i ∖ S_{i+1}` with its structure morphism to `S`.

The stratum `S_i ∖ S_{i+1}` is the open subscheme of `S_i` obtained by removing the support of
`I (i + 1)`. -/
def HasStratification (S : Scheme.{u}) (P : (T : Scheme.{u}) → (T ⟶ S) → Prop) : Prop :=
  ∃ (t : ℕ) (I : Fin (t + 1) → S.IdealSheafData),
    Stacks.Thickenings.IsThickening (I 0).subschemeι ∧
    (∀ i, (I i).IsFiniteType) ∧
    (∀ i : Fin t, I i.castSucc ≤ I i.succ) ∧
    I (Fin.last t) = ⊤ ∧
    ∀ i : Fin t,
      let Z := I i.castSucc
      let U : Z.subscheme.Opens := Z.subschemeι ⁻¹ᵁ (I i.succ).support.compl
      P U.toScheme (U.ι ≫ Z.subschemeι)

/-- A stratification for a stronger condition on the strata is one for a weaker condition. -/
theorem HasStratification.mono {S : Scheme.{u}}
    {P Q : (T : Scheme.{u}) → (T ⟶ S) → Prop}
    (hPQ : ∀ T a, P T a → Q T a) (hP : HasStratification S P) : HasStratification S Q := by
  obtain ⟨t, I, hthick, hfin, hmono, hlast, hstrat⟩ := hP
  exact ⟨t, I, hthick, hfin, hmono, hlast, fun i ↦ hPQ _ _ (hstrat i)⟩

/-! ### Finite strictly descending chains -/

/-- In a well-founded order with a least element, a relation that always allows a strict descent
from a nonempty element produces a finite strictly descending chain down to `⊥`. -/
theorem exists_finite_descending_chain {A : Type*} [PartialOrder A] [OrderBot A]
    [WellFoundedLT A] (P : A → A → Prop)
    (hP : ∀ a ≠ ⊥, ∃ b < a, P a b) (a : A) :
    ∃ (n : ℕ) (v : Fin (n + 1) → A), v 0 = a ∧ v (Fin.last n) = ⊥ ∧
      ∀ i : Fin n, v i.succ < v i.castSucc ∧ P (v i.castSucc) (v i.succ) := by
  classical
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    by_cases ha : a = ⊥
    · exact ⟨0, fun _ ↦ ⊥, ha.symm, rfl, Fin.elim0⟩
    obtain ⟨b, hba, hab⟩ := hP a ha
    obtain ⟨n, v, hv0, hvn, hv⟩ := ih b hba
    refine ⟨n + 1, Fin.cons a v, by simp, hvn, fun i ↦ ?_⟩
    refine Fin.cases ?_ (fun j ↦ hv j) i
    simpa [hv0] using And.intro hba hab

/-! ### The support of a vanishing ideal -/

/-- The support of the vanishing ideal of a closed subset is that subset. -/
theorem support_vanishingIdeal {S : Scheme.{u}} (C : Closeds S) :
    (Scheme.IdealSheafData.vanishingIdeal C).support = C :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal C)

/-! ### Noetherian induction -/

/-- The reduced closed subscheme on a closed set `C` has underlying set `C`. -/
private theorem range_subschemeι_vanishingIdeal {S : Scheme.{u}} (C : Closeds S) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base = (C : Set S) :=
  (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal C)

/-- Replacing a nonempty open subscheme of the reduced closed subscheme on a closed set `C` by
the closed set it removes from `C`. -/
private theorem exists_lt_closeds_of_nonempty_open {S : Scheme.{u}}
    (C : Closeds S)
    (U : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens) (hU : Nonempty U) :
    ∃ D : Closeds S, D < C ∧
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ D.compl = U := by
  have hj : Topology.IsClosedEmbedding
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base :=
    IsClosedImmersion.isClosedEmbedding _
  refine ⟨⟨_, hj.isClosedMap _ U.isOpen.isClosed_compl⟩, ?_, ?_⟩
  · refine lt_of_le_of_ne (fun s hs ↦ ?_) fun hDCeq ↦ ?_
    · have hs' : s ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base :=
        Set.image_subset_range _ _ hs
      rw [range_subschemeι_vanishingIdeal] at hs'
      exact hs'
    · obtain ⟨x⟩ := hU
      have hxC : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base x.1 ∈ (C : Set S) := by
        rw [← range_subschemeι_vanishingIdeal]
        exact ⟨x.1, rfl⟩
      exact (hj.injective.mem_set_image.mp (hDCeq.ge hxC)) x.property
  · refine TopologicalSpace.Opens.ext ?_
    change (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base ⁻¹'
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.base ''
          (U : Set (Scheme.IdealSheafData.vanishingIdeal C).subscheme)ᶜ)ᶜ =
      (U : Set (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
    rw [Set.preimage_compl, Set.preimage_image_eq _ hj.injective, compl_compl]

/-- **The Noetherian induction of Stacks 0H41.** Over a Noetherian base, if every nonempty closed
subset carries, on its reduced closed subscheme, a nonempty open subscheme satisfying `P`, then
the base has a `P`-stratification.

Over a Noetherian scheme every quasi-coherent ideal sheaf is of finite type, so the finite type
condition is automatic; the chain starts at the reduction of `S`, which is a thickening, and the
induction terminates because the space is Noetherian. -/
theorem exists_stratification_of_isNoetherian {S : Scheme.{u}} [IsNoetherian S]
    (P : (T : Scheme.{u}) → (T ⟶ S) → Prop)
    (hP : ∀ C : Closeds S, C ≠ ⊥ →
      ∃ U : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens,
        Nonempty U ∧ P U.toScheme (U.ι ≫
          (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)) :
    HasStratification S P := by
  classical
  obtain ⟨t, C, hC0, hCt, hC⟩ := exists_finite_descending_chain
    (fun C D : Closeds S ↦
      P (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ D.compl)).toScheme
        (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ D.compl).ι ≫
          (Scheme.IdealSheafData.vanishingIdeal C).subschemeι))
    (fun C hC ↦ by
      obtain ⟨U, hUne, hUP⟩ := hP C hC
      obtain ⟨D, hDC, hDU⟩ := exists_lt_closeds_of_nonempty_open C U hUne
      refine ⟨D, hDC, ?_⟩
      rw [hDU]
      exact hUP) ⊤
  refine ⟨t, fun i ↦ Scheme.IdealSheafData.vanishingIdeal (C i), ?_,
    fun i ↦ Scheme.IdealSheafData.isFiniteType_vanishingIdeal _,
    fun i ↦ Scheme.IdealSheafData.vanishingIdeal_antimono (hC i).1.le, ?_, ?_⟩
  · change Stacks.Thickenings.IsThickening
      (Scheme.IdealSheafData.vanishingIdeal (C 0)).subschemeι
    rw [Scheme.IdealSheafData.isThickening_subschemeι_iff, support_vanishingIdeal, hC0]
  · change Scheme.IdealSheafData.vanishingIdeal (C (Fin.last t)) = ⊤
    rw [hCt, Scheme.IdealSheafData.vanishingIdeal_bot]
  · intro i
    dsimp only
    rw [support_vanishingIdeal]
    exact (hC i).2

/-! ### Base change of a stratification -/

/-- **A stratification pulls back along any morphism of bases.** The closed subschemes are
replaced by their inverse images, which stay defined by finite type ideal sheaves by
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.comap`, and the condition on the strata is
transported by the assumed stability under precomposition. -/
theorem HasStratification.comap {S T : Scheme.{u}}
    {P : (U : Scheme.{u}) → (U ⟶ S) → Prop}
    (hP : ∀ {U V : Scheme.{u}} (a : U ⟶ S) (b : V ⟶ U), P U a → P V (b ≫ a))
    (hS : HasStratification S P) (g : T ⟶ S) :
    HasStratification T (fun U a ↦ P U (a ≫ g)) := by
  obtain ⟨t, I, hthick, hfin, hmono, hlast, hstrat⟩ := hS
  rw [Scheme.IdealSheafData.isThickening_subschemeι_iff] at hthick
  refine ⟨t, fun i ↦ (I i).comap g, ?_,
    fun i ↦ (hfin i).comap g,
    fun i ↦ Scheme.IdealSheafData.comap_mono g (hmono i), ?_, ?_⟩
  · change Stacks.Thickenings.IsThickening ((I 0).comap g).subschemeι
    rw [Scheme.IdealSheafData.isThickening_subschemeι_iff,
      Scheme.IdealSheafData.support_comap, hthick]
    exact TopologicalSpace.Closeds.ext (by simp)
  · change (I (Fin.last t)).comap g = ⊤
    rw [hlast, Scheme.IdealSheafData.comap_top]
  · intro i
    dsimp only
    have hq : ((I i.castSucc).comap g).subschemeι ≫ g =
        (((I i.castSucc).comapIso g).hom ≫ pullback.snd g (I i.castSucc).subschemeι) ≫
          (I i.castSucc).subschemeι := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst (I i.castSucc) g, Category.assoc,
        Category.assoc, ← pullback.condition]
    have hW : (((I i.castSucc).comapIso g).hom ≫ pullback.snd g (I i.castSucc).subschemeι) ⁻¹ᵁ
        ((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl) =
        ((I i.castSucc).comap g).subschemeι ⁻¹ᵁ ((I i.succ).comap g).support.compl := by
      refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
      change ((((I i.castSucc).comapIso g).hom ≫ pullback.snd g (I i.castSucc).subschemeι) ≫
          (I i.castSucc).subschemeι).base x ∉ ((I i.succ).support : Set S) ↔
        ((I i.castSucc).comap g).subschemeι.base x ∉
          (((I i.succ).comap g).support : Set T)
      rw [Scheme.IdealSheafData.support_comap, ← hq]
      change (((I i.castSucc).comap g).subschemeι ≫ g).base x ∉ _ ↔
        ((I i.castSucc).comap g).subschemeι.base x ∉
          (g.base ⁻¹' ((I i.succ).support : Set S))
      rfl
    have hb := hP ((((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl)).ι ≫
        (I i.castSucc).subschemeι)
      (Scheme.homOfLE _ hW.ge ≫
        (((I i.castSucc).comapIso g).hom ≫ pullback.snd g (I i.castSucc).subschemeι) ∣_
          ((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl))
      (by dsimp only at hstrat; exact hstrat i)
    refine cast (congrArg _ ?_) hb
    rw [Category.assoc, ← Category.assoc (_ ∣_ _),
      (isPullback_morphismRestrict
        (((I i.castSucc).comapIso g).hom ≫ pullback.snd g (I i.castSucc).subschemeι)
        ((I i.castSucc).subschemeι ⁻¹ᵁ (I i.succ).support.compl)).w,
      Category.assoc, ← hq, ← Category.assoc, Scheme.homOfLE_ι, Category.assoc]

/-! ### Descent to a Noetherian base -/

/-- The absolute Noetherian approximation of a quasi-compact quasi-separated scheme, obtained
from Stacks 07RN applied to its empty open subscheme. -/
noncomputable def finiteTypeApproximation {S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] :
    Scheme.FiniteTypeApproximation
      ((Functor.const (PUnit.{u + 1})ᵒᵈ).obj (⊥ : S.Opens).toScheme)
      S ⊥ (𝟙 _) := by
  let E : Scheme.{u} := (⊥ : S.Opens).toScheme
  have : IsEmpty E := by
    change IsEmpty {x : S // x ∈ (⊥ : S.Opens)}
    exact ⟨fun x ↦ x.property⟩
  let D := (Functor.const (PUnit.{u + 1})ᵒᵈ).obj E
  have : ∀ {i j : (PUnit.{u + 1})ᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f) := by
    intro i j f
    change IsAffineHom (𝟙 E)
    infer_instance
  have : ∀ i, LocallyOfFiniteType (terminal.from (D.obj i)) := by
    intro i
    change LocallyOfFiniteType (terminal.from E)
    infer_instance
  have : ∀ i, QuasiCompact (terminal.from (D.obj i)) := by
    intro i
    change QuasiCompact (terminal.from E)
    infer_instance
  exact finiteTypeApproximationOfIsLimit D S ⊥ (𝟙 _)
    { lift := fun c ↦ c.π.app PUnit.unit
      fac := by
        intro c j
        have : j = PUnit.unit := Subsingleton.elim _ _
        subst j
        exact Category.comp_id _
      uniq := by intros; aesop }

/-- A morphism of finitely presented schemes over the limit of a cofiltered system with affine
transition morphisms descends to one of the stages. -/
theorem exists_morphism_model {I : Type*} [Category I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (X Y : Over c.pt) (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    ∃ (i : I) (Xi Yi : Over (D.obj i)) (fi : Xi ⟶ Yi)
      (eX : X ≅ (Over.pullback (c.π.app i)).obj Xi)
      (eY : Y ≅ (Over.pullback (c.π.app i)).obj Yi),
      FinitePresentation Xi.hom ∧ FinitePresentation Yi.hom ∧
      f ≫ eY.hom = eX.hom ≫ (Over.pullback (c.π.app i)).map fi := by
  obtain ⟨i, Xi, hXi, ⟨ei⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc X hX
  obtain ⟨j, Yj, hYj, ⟨ej⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc Y hY
  obtain ⟨k, ki, kj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  let Xk := (Over.pullback (D.map ki)).obj Xi
  let Yk := (Over.pullback (D.map kj)).obj Yj
  have hXk := finitePresentation_pullback (D.map ki) Xi hXi
  have hYk := finitePresentation_pullback (D.map kj) Yj hYj
  let eX : X ≅ (Over.pullback (c.π.app k)).obj Xk :=
    ei ≪≫ eqToIso (congrArg (fun g ↦ (Over.pullback g).obj Xi) (c.w ki).symm) ≪≫
      (Over.pullbackComp (c.π.app k) (D.map ki)).app Xi
  let eY : Y ≅ (Over.pullback (c.π.app k)).obj Yk :=
    ej ≪≫ eqToIso (congrArg (fun g ↦ (Over.pullback g).obj Yj) (c.w kj).symm) ≪≫
      (Over.pullbackComp (c.π.app k) (D.map kj)).app Yj
  obtain ⟨l, lk, fl, a, b, -, -, hab⟩ :=
    exists_morphism_after_baseChange D c hc k Xk Yk hXk hYk (eX.inv ≫ f ≫ eY.hom)
  refine ⟨l, _, _, fl, eX ≪≫ a.symm, eY ≪≫ b.symm,
    finitePresentation_pullback (D.map lk) Xk hXk,
    finitePresentation_pullback (D.map lk) Yk hYk, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← cancel_mono b.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hab]
  simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

/-- **Descent to a Noetherian base.** A morphism between schemes of finite presentation over a
quasi-compact quasi-separated base is, up to isomorphism, the base change of such a morphism over
a Noetherian base. -/
theorem exists_noetherian_morphism_model {S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (X Y : Over S) (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    ∃ T : Scheme.{u}, IsNoetherian T ∧
      ∃ (g : S ⟶ T) (XT YT : Over T) (fT : XT ⟶ YT)
        (eX : X ≅ (Over.pullback g).obj XT) (eY : Y ≅ (Over.pullback g).obj YT),
        FinitePresentation XT.hom ∧ FinitePresentation YT.hom ∧
        f ≫ eY.hom = eX.hom ≫ (Over.pullback g).map fT := by
  let a := finiteTypeApproximation (S := S)
  let _ := a.indexPreorder
  have := a.indexNonempty
  have := a.indexDirected
  let D := a.ambient
  let c : Cone D := Cone.mk S a.ambientCone
  have : ∀ {i j : a.indexTypeᵒᵈ} (e : i ⟶ j), IsAffineHom (D.map e) := a.transition_affine
  have : ∀ i, LocallyOfFiniteType (terminal.from (D.obj i)) := a.locallyOfFiniteType
  have : ∀ i, QuasiCompact (terminal.from (D.obj i)) := a.quasiCompact
  have : ∀ i, IsNoetherian (D.obj i) := fun i ↦
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from (D.obj i)
  obtain ⟨i, Xi, Yi, fi, eX, eY, hXi, hYi, hf⟩ :=
    exists_morphism_model D c a.ambientCone_isLimit X Y f hX hY
  exact ⟨D.obj i, inferInstance, c.π.app i, Xi, Yi, fi, eX, eY, hXi, hYi, hf⟩

end Stacks.GenericFlatness

namespace AlgebraicGeometry

open Stacks.GenericFlatness

/-- **The conclusion of Stacks 0H41 for one morphism `f : X ⟶ Y` over `S`.** There is a finite
descending chain of closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` of the base, recorded by the
ascending chain `I` of their ideal sheaves, such that

* each `S_i → S` is defined by a finite type ideal sheaf,
* `S₀ ⊆ S` is a thickening, and
* formation of the scheme-theoretic image of the base change of `f` to the stratum
  `S_i ∖ S_{i+1}` commutes with arbitrary base change,

where `S_i ∖ S_{i+1}` is the open subscheme of `S_i` on the complement of the support of
`I (i + 1)`. -/
def HasImageBaseChangeStratification {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) : Prop :=
  HasStratification S fun _ g ↦ ImageCommutesWithBaseChange ((Over.pullback g).map f)

/-- **Stacks Project, Tag 0H41.** Let `S` be a quasi-compact and quasi-separated scheme and
`f : X ⟶ Y` a morphism of schemes over `S` with both `X` and `Y` of finite presentation over `S`.
Then there are a `t ≥ 0` and closed subschemes `S ⊇ S₀ ⊇ S₁ ⊇ ⋯ ⊇ S_t = ∅` such that each
`S_i → S` is defined by a finite type ideal sheaf, `S₀ ⊆ S` is a thickening, and formation of the
scheme-theoretic image of the base change of `f` to each stratum `S_i ∖ S_{i+1}` commutes with
arbitrary base change. -/
@[stacks 0H41]
theorem hasImageBaseChangeStratification {S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (X Y : Over S) (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    HasImageBaseChangeStratification f := by
  have main : HasStratification S fun _ g ↦
      ImageCommutesWithBaseChange ((Over.pullback g).map f) := ?main
  · exact main
  have hnoeth : ∀ (T : Scheme.{u}) [IsNoetherian T] (X Y : Over T) (f : X ⟶ Y),
      FinitePresentation X.hom → FinitePresentation Y.hom →
      HasStratification T fun _ g ↦
        ImageCommutesWithBaseChange ((Over.pullback g).map f) := by
    intro T _ X Y f hX hY
    refine exists_stratification_of_isNoetherian _ fun C hC ↦ ?_
    set J := Scheme.IdealSheafData.vanishingIdeal C with hJ
    have : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
    have : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
    have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    have : IsNoetherian J.subscheme := ⟨⟩
    have : Nonempty J.subscheme := by
      have hCne : (C : Set T).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr fun h ↦ hC (SetLike.coe_injective h)
      rw [← range_subschemeι_vanishingIdeal] at hCne
      obtain ⟨-, y, -⟩ := hCne
      exact ⟨y⟩
    obtain ⟨U, hU, hfU⟩ := exists_good_open_of_isReduced J.subscheme
      ((Over.pullback J.subschemeι).obj X) ((Over.pullback J.subschemeι).obj Y)
      ((Over.pullback J.subschemeι).map f)
      (finitePresentation_pullback J.subschemeι X hX)
      (finitePresentation_pullback J.subschemeι Y hY)
    exact ⟨U, hU, imageCommutesWithBaseChange_of_isIso
      ((Over.pullbackComp U.ι J.subschemeι).app X)
      ((Over.pullbackComp U.ι J.subschemeι).app Y)
      ((Over.pullbackComp U.ι J.subschemeι).hom.naturality f) hfU⟩
  obtain ⟨T, hT, g, XT, YT, fT, eX, eY, hXT, hYT, he⟩ :=
    exists_noetherian_morphism_model X Y f hX hY
  have := hT
  have hstrat := HasStratification.comap
    (P := fun _ a ↦ ImageCommutesWithBaseChange ((Over.pullback a).map fT))
    (fun a b h ↦ imageCommutesWithBaseChange_comp a b h)
    (hnoeth T XT YT fT hXT hYT) g
  refine HasStratification.mono (P := fun _ a ↦
    ImageCommutesWithBaseChange ((Over.pullback (a ≫ g)).map fT)) ?_ hstrat
  intro U a ha
  have hiter : ImageCommutesWithBaseChange ((Over.pullback a).map
      ((Over.pullback g).map fT)) := imageCommutesWithBaseChange_of_isIso
    ((Over.pullbackComp a g).symm.app XT) ((Over.pullbackComp a g).symm.app YT)
    ((Over.pullbackComp a g).inv.naturality fT) ha
  intro T'' k
  exact imageCommutesWithBaseChange_of_isIso
    (f := (Over.pullback a).map ((Over.pullback g).map fT))
    (f' := (Over.pullback a).map f)
    ((Over.pullback a).mapIso eX) ((Over.pullback a).mapIso eY)
    (by simpa only [Functor.map_comp, Functor.mapIso_hom] using
      congrArg ((Over.pullback a).map) he) hiter k


end AlgebraicGeometry

end
