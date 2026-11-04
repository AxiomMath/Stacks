module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDiagramCone
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.BaseChange

/-!
# Morphisms of `Coh_{X/Y}` are determined by, and glue from, their restrictions to an fpqc covering

Let `A`, `A'` be objects of `Coh_{X/Y}` (Stacks 08KB) and `β : A.T ⟶ A'.T` a morphism of test
schemes over `Y`.  Let `{φ l : A_l ⟶ A}` be morphisms of `Coh_{X/Y}` whose induced morphisms of
base changes `X_{A_l} ⟶ X_A` form an fpqc covering of algebraic spaces.

* Two morphisms `A ⟶ A'` over `β` which agree after composing with every `φ l` are equal
  (`AlgebraicGeometry.Space.CoherentHom.eq_of_comp_eq`): their module comparisons have the same
  inverse images along the covering, and inverse image along an fpqc covering is faithful
  (Stacks 04W8).
* Morphisms `ψ l : A_l ⟶ A'` over `φ l ≫ β` which agree on objects over the pairwise fibre
  products come from a morphism `A ⟶ A'` over `β`
  (`AlgebraicGeometry.Space.CoherentHom.exists_glue`): the module comparisons of the `ψ l`, read
  through those of the `φ l`, are a family of isomorphisms between the inverse images of the two
  quasi-coherent modules `X_β^* F'` and `F` satisfying the pairwise condition of Stacks 04W3, so
  they are the inverse images of one isomorphism (Stacks 04W8).

These are the two halves of the sheaf property of the morphisms of `Coh_{X/Y}` in the proof of
Stacks 08KC.

## Main results

* `AlgebraicGeometry.Space.spanIsoOf_eq_of_comp_eq_refl`: the converse reading of
  `AlgebraicGeometry.Space.spanIsoOf_comp_eq_refl`.
* `AlgebraicGeometry.Space.CoherentHom.spanIso_eq_of_comp_eq`: the span isomorphism of two
  morphisms out of a common source, through a commuting square.
* `AlgebraicGeometry.Space.CoherentHom.eq_of_comp_eq`: **faithfulness.**
* `AlgebraicGeometry.Space.CoherentHom.exists_glue`: **gluing.**

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (pullbackComparison pair pairFst pairSnd
  pair_condition restrictForm)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The converse reading of a cocone.**  In the situation of
`AlgebraicGeometry.Space.spanIsoOf_comp_eq_refl`, if the span isomorphism along `r` of the two
composite comparisons is the identity, then the span isomorphism of `εc` and `εe` along `r` is
the inverse of the reading of `ζ₁` followed by the reading of `ζ₂`. -/
theorem spanIsoOf_eq_of_comp_eq_refl {Z X_Q X₁ X₂ X₀ : AlgebraicSpaces B S hS}
    {F_Q : Modules.{u, u} B S hS X_Q.1 X_Q.2} {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2}
    {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2} {M : Modules.{u, u} B S hS X₀.1 X₀.2}
    (c' : X_Q ⟶ X₁) (e' : X_Q ⟶ X₂) (εc : (modulePullback B S hS c').obj F₁ ≅ F_Q)
    (εe : (modulePullback B S hS e').obj F₂ ≅ F_Q) (a₁ : X₁ ⟶ X₀) (a₂ : X₂ ⟶ X₀)
    (ζ₁ : (modulePullback B S hS a₁).obj M ≅ F₁) (ζ₂ : (modulePullback B S hS a₂).obj M ≅ F₂)
    (k₁ k₂ : X_Q ⟶ X₀) (hk₁ : c' ≫ a₁ = k₁) (hk₂ : e' ≫ a₂ = k₂)
    (κ₁ : (modulePullback B S hS k₁).obj M ≅ F_Q) (κ₂ : (modulePullback B S hS k₂).obj M ≅ F_Q)
    (hκ₁ : κ₁ = pullbackComparison B S hS c' a₁ k₁ hk₁ M ≪≫
      (modulePullback B S hS c').mapIso ζ₁ ≪≫ εc)
    (hκ₂ : κ₂ = pullbackComparison B S hS e' a₂ k₂ hk₂ M ≪≫
      (modulePullback B S hS e').mapIso ζ₂ ≪≫ εe)
    (r : Z ⟶ X_Q) (p₁ : Z ⟶ X₁) (p₂ : Z ⟶ X₂) (hp₁ : r ≫ c' = p₁) (hp₂ : r ≫ e' = p₂)
    (rx : Z ⟶ X₀) (hx₁ : p₁ ≫ a₁ = rx) (hx₂ : p₂ ≫ a₂ = rx)
    (h₁ : r ≫ k₁ = rx) (h₂ : r ≫ k₂ = rx)
    (h : spanIsoOf k₁ k₂ κ₁ κ₂ r rx rx h₁ h₂ = Iso.refl _) :
    spanIsoOf c' e' εc εe r p₁ p₂ hp₁ hp₂ =
      (readOf a₁ ζ₁ p₁ rx hx₁).symm ≪≫ readOf a₂ ζ₂ p₂ rx hx₂ := by
  rw [spanIsoOf_eq_readOf,
    readOf_comp c' εc a₁ ζ₁ k₁ hk₁ κ₁ hκ₁ r p₁ hp₁ rx h₁ hx₁,
    readOf_comp e' εe a₂ ζ₂ k₂ hk₂ κ₂ hκ₂ r p₂ hp₂ rx h₂ hx₂] at h
  rw [spanIsoOf_eq_readOf]
  have h' := congrArg (fun z => (readOf a₁ ζ₁ p₁ rx hx₁).symm ≪≫ z ≪≫ readOf a₂ ζ₂ p₂ rx hx₂) h
  simpa only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
    Iso.trans_refl, Iso.refl_trans] using h'

/-- **The restricted reading of a comparison read through two module comparisons.**  For
`a : X ⟶ X₀`, `X_β : X₀ ⟶ X'` with composite `k`, module comparisons `ζA : a^*N ≅ F` and
`ζB : k^*G ≅ F`, the morphism `a^*(X_β^*G) ⟶ a^*N` they induce, restricted along `p : Z ⟶ X`, is
the comparison of Stacks 03LU followed by the reading of `ζB` and the inverse of the reading of
`ζA`. -/
theorem restrictForm_eq_readOf {Z X X₀ X' : AlgebraicSpaces B S hS}
    {N : Modules.{u, u} B S hS X₀.1 X₀.2} {G : Modules.{u, u} B S hS X'.1 X'.2}
    {F : Modules.{u, u} B S hS X.1 X.2} (a : X ⟶ X₀) (kB : X₀ ⟶ X') (k : X ⟶ X')
    (hk : a ≫ kB = k) (ζA : (modulePullback B S hS a).obj N ≅ F)
    (ζB : (modulePullback B S hS k).obj G ≅ F) (p : Z ⟶ X) (rx : Z ⟶ X₀) (hp : p ≫ a = rx)
    (rxB : Z ⟶ X') (hB : rx ≫ kB = rxB) (hpB : p ≫ k = rxB) :
    restrictForm B S hS p a rx hp
        ((pullbackComparison B S hS a kB k hk G).symm ≪≫ ζB ≪≫ ζA.symm).hom =
      ((pullbackComparison B S hS rx kB rxB hB G).symm ≪≫ readOf k ζB p rxB hpB ≪≫
        (readOf a ζA p rx hp).symm).hom := by
  have t := QuasiCoherentDescent.pullbackComparison_trans B S hS p a kB k hk rx hp rxB hpB hB G
  have t' : pullbackComparison B S hS p a rx hp ((modulePullback B S hS kB).obj G) =
      (pullbackComparison B S hS rx kB rxB hB G).symm ≪≫
        pullbackComparison B S hS p k rxB hpB G ≪≫
          (modulePullback B S hS p).mapIso (pullbackComparison B S hS a kB k hk G) := by
    rw [t, Iso.symm_self_id_assoc]
  have hiso : pullbackComparison B S hS p a rx hp ((modulePullback B S hS kB).obj G) ≪≫
      (modulePullback B S hS p).mapIso
        ((pullbackComparison B S hS a kB k hk G).symm ≪≫ ζB ≪≫ ζA.symm) ≪≫
      (pullbackComparison B S hS p a rx hp N).symm =
        (pullbackComparison B S hS rx kB rxB hB G).symm ≪≫ readOf k ζB p rxB hpB ≪≫
          (readOf a ζA p rx hp).symm := by
    rw [t']
    simp only [readOf, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm,
      Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [restrictForm, QuasiCoherentDescent.factorForm, ← Functor.mapIso_hom, ← Iso.symm_hom,
    ← Iso.trans_hom, ← Iso.trans_hom, hiso]

/-- Two readings of one isomorphism, compared. -/
theorem _root_.CategoryTheory.Iso.trans_symm_eq_of_symm_trans_eq {C : Type*} [Category C]
    {X Y₁ Y₂ Z : C} (a₁ : X ≅ Y₁) (a₂ : X ≅ Y₂) (b₁ : Z ≅ Y₁) (b₂ : Z ≅ Y₂)
    (h : a₁.symm ≪≫ a₂ = b₁.symm ≪≫ b₂) : b₁ ≪≫ a₁.symm = b₂ ≪≫ a₂.symm := by
  have h' := congrArg (fun z => b₁ ≪≫ z ≪≫ a₂.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.self_symm_id_assoc, Iso.trans_refl,
    Iso.symm_self_id_assoc] using h'

namespace CoherentHom

variable {D : CoherentSituation B S hS}

/-- Two morphisms of `Coh_{X/Y}` with the same base map and equal module comparisons are equal. -/
theorem mk_congr_fibre {A A' : CoherentObject D} {b : A.T ⟶ A'.T}
    {f f' : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F} (h : f = f')
    (i : IsIso f) (i' : IsIso f') : (⟨b, f, i⟩ : CoherentHom A A') = ⟨b, f', i'⟩ := by
  subst h
  rfl

/-- A morphism of `Coh_{X/Y}` with its base map rewritten along an equality, its module comparison
transported along the induced identification of inverse images. -/
theorem mk_eq_mk_eqToHom {A A' : CoherentObject D} {b b' : A.T ⟶ A'.T} (h : b = b')
    (f : (modulePullback B S hS (D.relativeMap b')).obj A'.F ⟶ A.F) [IsIso f] :
    (⟨b', f, inferInstance⟩ : CoherentHom A A') =
      ⟨b, eqToHom (congrArg (fun b => (modulePullback B S hS (D.relativeMap b)).obj A'.F) h) ≫ f,
        inferInstance⟩ := by
  subst h
  exact mk_congr_fibre (by simp only [eqToHom_refl, Category.id_comp]) _ _

/-- The composite of a morphism of `Coh_{X/Y}` with one given by its components. -/
theorem comp_mk_eq {Aₗ A A' : CoherentObject D} (φ : CoherentHom Aₗ A) (b : A.T ⟶ A'.T)
    (g : (modulePullback B S hS (D.relativeMap b)).obj A'.F ⟶ A.F) (i : IsIso g)
    (f' : (modulePullback B S hS (D.relativeMap (φ.base ≫ b))).obj A'.F ⟶ Aₗ.F) (i' : IsIso f')
    (h : Functor.fibreComp (D.compComparison φ.base b) φ.fibre g = f') :
    φ.comp ⟨b, g, i⟩ = ⟨φ.base ≫ b, f', i'⟩ := by
  subst h
  rfl

/-- **The span isomorphism through a commuting square.**  If `c : Q ⟶ A₁` and `e : Q ⟶ A₂`
followed by `φ₁ : A₁ ⟶ A` and `φ₂ : A₂ ⟶ A` agree, then the span isomorphism of `c` and `e`
along any `r : Z ⟶ X_Q` is the inverse of the reading of the module comparison of `φ₁` followed
by the reading of that of `φ₂`. -/
theorem spanIso_eq_of_comp_eq {Q A₁ A₂ A : CoherentObject D} (c : CoherentHom Q A₁)
    (e : CoherentHom Q A₂) (φ₁ : CoherentHom A₁ A) (φ₂ : CoherentHom A₂ A)
    (hce : c.comp φ₁ = e.comp φ₂) {Z : AlgebraicSpaces B S hS} (r : Z ⟶ D.space Q.T)
    (p₁ : Z ⟶ D.space A₁.T) (p₂ : Z ⟶ D.space A₂.T) (hp₁ : r ≫ D.relativeMap c.base = p₁)
    (hp₂ : r ≫ D.relativeMap e.base = p₂) (rx : Z ⟶ D.space A.T)
    (hx₁ : p₁ ≫ D.relativeMap φ₁.base = rx) (hx₂ : p₂ ≫ D.relativeMap φ₂.base = rx) :
    spanIso c e r p₁ p₂ hp₁ hp₂ =
      (readOf (D.relativeMap φ₁.base) (asIso φ₁.fibre) p₁ rx hx₁).symm ≪≫
        readOf (D.relativeMap φ₂.base) (asIso φ₂.fibre) p₂ rx hx₂ := by
  have hk₁ : D.relativeMap c.base ≫ D.relativeMap φ₁.base = D.relativeMap (c.comp φ₁).base :=
    (CoherentSituation.relativeMap_comp D _ _).symm
  have hk₂ : D.relativeMap e.base ≫ D.relativeMap φ₂.base = D.relativeMap (e.comp φ₂).base :=
    (CoherentSituation.relativeMap_comp D _ _).symm
  have h₁ : r ≫ D.relativeMap (c.comp φ₁).base = rx := by
    rw [← hk₁, ← Category.assoc, hp₁, hx₁]
  have h₂ : r ≫ D.relativeMap (e.comp φ₂).base = rx := by
    rw [← hk₂, ← Category.assoc, hp₂, hx₂]
  have href : spanIso (c.comp φ₁) (e.comp φ₂) r rx rx h₁ h₂ = Iso.refl _ := by
    rw [spanIso_congr rx rx rfl hce.symm rfl h₁ h₂]
    exact spanIso_refl _ _ _ _
  rw [spanIso_eq_spanIsoOf] at href
  rw [spanIso_eq_spanIsoOf]
  refine spanIsoOf_eq_of_comp_eq_refl (D.relativeMap c.base) (D.relativeMap e.base)
    (asIso c.fibre) (asIso e.fibre) (D.relativeMap φ₁.base) (D.relativeMap φ₂.base)
    (asIso φ₁.fibre) (asIso φ₂.fibre) _ _ hk₁ hk₂ _ _ ?_ ?_ r p₁ p₂ hp₁ hp₂ rx hx₁ hx₂ h₁ h₂
    href <;>
  (rw [asIso_comp_fibre, D.compComparison_app]; rfl)

/-- **Morphisms of `Coh_{X/Y}` are determined by their restrictions to an fpqc covering.**  Two
morphisms `A ⟶ A'` with the same base map which agree after composing with each member of a
family `{φ l : A_l ⟶ A}` whose morphisms of base changes form an fpqc covering are equal. -/
theorem eq_of_comp_eq {A A' : CoherentObject D} {L : Type v} {Aₗ : L → CoherentObject D}
    (φ : ∀ l, CoherentHom (Aₗ l) A)
    (hφ : IsFpqcCovering B S hS fun l => (D.relativeMap (φ l).base).hom)
    (m n : CoherentHom A A') (hb : m.base = n.base) (h : ∀ l, (φ l).comp m = (φ l).comp n) :
    m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  have hl : ∀ l, (modulePullback B S hS (D.relativeMap (φ l).base)).map mf =
      (modulePullback B S hS (D.relativeMap (φ l).base)).map nf := by
    intro l
    have hfib : Functor.fibreComp (D.compComparison (φ l).base mb) (φ l).fibre mf =
        Functor.fibreComp (D.compComparison (φ l).base mb) (φ l).fibre nf :=
      eq_of_heq (CoherentHom.mk.inj (h l)).2
    exact (Iso.cancel_iso_hom_right _ _ (asIso (φ l).fibre)).1
      ((Iso.cancel_iso_hom_left ((D.compComparison (φ l).base mb).app A'.F) _ _).1 hfib)
  have := QuasiCoherentDescent.modulePullback_map_injective_of_isFpqcCovering B S hS
    (QuasiCoherentDescent.reprFpqcHomInjective.{u, v} B S hS) _ _ hφ mf nf hl
  subst this
  rfl

/-- **Morphisms of `Coh_{X/Y}` glue along an fpqc covering.**  Let `{φ l : A_l ⟶ A}` be a family
whose morphisms of base changes form an fpqc covering, and `β : A.T ⟶ A'.T`.  Morphisms
`A_l ⟶ A'` over `φ l ≫ β`, given by module comparisons `ψ l`, which agree after composing with
the two morphisms out of an object over each pairwise fibre product, come from a morphism
`A ⟶ A'` over `β`. -/
theorem exists_glue {A A' : CoherentObject D} (β : A.T ⟶ A'.T) {L : Type v}
    {Aₗ : L → CoherentObject D} (φ : ∀ l, CoherentHom (Aₗ l) A)
    (hφ : IsFpqcCovering B S hS fun l => (D.relativeMap (φ l).base).hom)
    (ψ : ∀ l, (modulePullback B S hS (D.relativeMap ((φ l).base ≫ β))).obj A'.F ⟶ (Aₗ l).F)
    [hψ : ∀ l, IsIso (ψ l)]
    (hpair : ∀ l m, ∃ (Q : CoherentObject D) (c : CoherentHom Q (Aₗ l))
      (e : CoherentHom Q (Aₗ m)),
      IsPullback c.base.left e.base.left (φ l).base.left (φ m).base.left ∧
        c.comp (φ l) = e.comp (φ m) ∧
        c.comp ⟨(φ l).base ≫ β, ψ l, hψ l⟩ = e.comp ⟨(φ m).base ≫ β, ψ m, hψ m⟩) :
    ∃ G : CoherentHom A A', G.base = β ∧ ∀ l, (φ l).comp G = ⟨(φ l).base ≫ β, ψ l, hψ l⟩ := by
  have hk : ∀ l, D.relativeMap (φ l).base ≫ D.relativeMap β =
      D.relativeMap ((φ l).base ≫ β) := fun l => (CoherentSituation.relativeMap_comp D _ _).symm
  have hM' : ((modulePullback B S hS (D.relativeMap β)).obj A'.F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A'.F A'.quasicoherent
  let w : ∀ l, (modulePullback B S hS (D.relativeMap (φ l).base)).obj
      ((modulePullback B S hS (D.relativeMap β)).obj A'.F) ⟶
        (modulePullback B S hS (D.relativeMap (φ l).base)).obj A.F :=
    fun l => ((pullbackComparison B S hS (D.relativeMap (φ l).base) (D.relativeMap β) _ (hk l)
      A'.F).symm ≪≫ asIso (ψ l) ≪≫ (asIso (φ l).fibre).symm).hom
  have hw : QuasiCoherentDescent.IsPairwiseCompatible B S hS (fun l => D.space (Aₗ l).T)
      (fun l => D.relativeMap (φ l).base) w := by
    refine QuasiCoherentDescent.isPairwiseCompatible_of_restrictForm_eq _ _ w fun l m => ?_
    obtain ⟨Q, c, e, hsq, hφce, hψce⟩ := hpair l m
    have hpb := isPullback_baseChangeMap_of_isPullback D.f hsq
    let p₁ := pairFst B S hS (fun l => D.space (Aₗ l).T) (fun l => D.relativeMap (φ l).base) l m
    let p₂ := pairSnd B S hS (fun l => D.space (Aₗ l).T) (fun l => D.relativeMap (φ l).base) l m
    have hcond : p₂ ≫ D.relativeMap (φ m).base = p₁ ≫ D.relativeMap (φ l).base :=
      (pair_condition B S hS _ _ l m).symm
    let r := hpb.lift p₁ p₂ hcond.symm
    have hr₁ : r ≫ D.relativeMap c.base = p₁ := hpb.lift_fst _ _ _
    have hr₂ : r ≫ D.relativeMap e.base = p₂ := hpb.lift_snd _ _ _
    have hxB₁ : p₁ ≫ D.relativeMap ((φ l).base ≫ β) =
        (p₁ ≫ D.relativeMap (φ l).base) ≫ D.relativeMap β := by
      rw [← hk l, Category.assoc]
    have hxB₂ : p₂ ≫ D.relativeMap ((φ m).base ≫ β) =
        (p₁ ≫ D.relativeMap (φ l).base) ≫ D.relativeMap β := by
      rw [← hk m, ← Category.assoc, hcond]
    have τA := spanIso_eq_of_comp_eq c e (φ l) (φ m) hφce r _ _ hr₁ hr₂ _ rfl hcond
    have τB := spanIso_eq_of_comp_eq c e ⟨(φ l).base ≫ β, ψ l, hψ l⟩
      ⟨(φ m).base ≫ β, ψ m, hψ m⟩ hψce r _ _ hr₁ hr₂ _ hxB₁ hxB₂
    rw [restrictForm_eq_readOf (D.relativeMap (φ l).base) (D.relativeMap β) _ (hk l)
      (asIso (φ l).fibre) (asIso (ψ l)) p₁ _ rfl _ rfl hxB₁,
      restrictForm_eq_readOf (D.relativeMap (φ m).base) (D.relativeMap β) _ (hk m)
      (asIso (φ m).fibre) (asIso (ψ m)) p₂ _ hcond _ rfl hxB₂]
    rw [Iso.trans_symm_eq_of_symm_trans_eq _ _ _ _ (τA.symm.trans τB)]
  obtain ⟨g, hg, -⟩ := QuasiCoherentDescent.existsUnique_modulePullback_map_eq
    (fun l => D.space (Aₗ l).T) (fun l => D.relativeMap (φ l).base) hφ hM' A.quasicoherent w hw
  have hg' : ∀ l, (modulePullback B S hS (D.relativeMap (φ l).base)).map g = w l := hg
  have hgi : IsIso g := reflectsIsoAlongFpqcCovering _ hφ _ A.F hM' A.quasicoherent g
    fun l => by rw [hg l]; infer_instance
  refine ⟨⟨β, g, hgi⟩, rfl, fun l => comp_mk_eq (φ l) β g hgi (ψ l) (hψ l) ?_⟩
  have hc : (D.compComparison (φ l).base β).hom.app A'.F =
      (pullbackComparison B S hS (D.relativeMap (φ l).base) (D.relativeMap β) _ (hk l) A'.F).hom :=
    congrArg Iso.hom (D.compComparison_app (φ l).base β A'.F)
  rw [Functor.fibreComp, hc, hg' l]
  simp only [w, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc, IsIso.inv_hom_id, Category.comp_id]

end CoherentHom

end AlgebraicGeometry.Space

end
