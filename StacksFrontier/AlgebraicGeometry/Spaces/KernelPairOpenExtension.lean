module

public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.ExtensionAlongOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.Slice
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleRelationChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale equivalence relation extending the kernel pair of an étale map from an open

Let `V` be an object of the big fppf site of `S`, let `j : W ⟶ V` be an open immersion of
objects of the site, and let `p : W ⟶ X` be an étale morphism to a presheaf `X` whose kernel pair
is represented by `q₁, q₂ : Q ⟶ W`. Glueing `V` to `Q` along the diagonal copy of `W` gives an
object `R` of the site with two morphisms `t, s : R ⟶ V`, the identity on `V` and `q₁ ≫ j`,
resp. `q₂ ≫ j`, on `Q`. This file proves that `(t, s)` is an étale equivalence relation on `V`,
so that by Stacks 02WW its quotient is an algebraic space.

It is the relation `R_i = V_i ⊔_{W_i} (W_i ×_{U_i} W_i)` on `V_i` of the proof of absolute
Noetherian approximation for algebraic spaces, Stacks 07SU, with `X = U_i`.

## Main definitions

* `AlgebraicGeometry.Space.OpenKernelPairExtension`: the data `j`, `p` and a representing kernel
  pair, together with the glued object `R` of the site and its two morphisms to `V`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_comp_eq_id_of_etale`: a section of an étale morphism of
  schemes is an open immersion.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.equivalenceRelation_kernel`: the kernel pair
  of a morphism from an object of the site is an equivalence relation of *schemes*, tested
  against all schemes and not only those of the site.
* `AlgebraicGeometry.Space.OpenKernelPairExtension.isEtaleEquivalenceRelation`: the glued pair
  `(t, s)` is an étale equivalence relation over `S`.

## Implementation notes

The kernel pair is a kernel pair of presheaves on the site, so its universal property only sees
objects of the site; the equivalence relation of Stacks 022P is one of schemes over `S`, tested
against all schemes. The two are connected by testing against the universal objects, which do
lie in the site: joint monicity is the equality of the two projections of the scheme
`Q ×_{W ×_S W} Q`, and transitivity is a lift on `Q ×_W Q`; both are fibre products of objects of
the site, hence objects of the site by Stacks 000R.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

/-- A section of a morphism is the base change of its diagonal along the morphism
`(δ ∘ t, id) : T ⟶ T ×_W T`. -/
theorem isPullback_section_diagonal {C : Type*} [Category C] {T W : C} (t : T ⟶ W)
    [HasPullback t t] (δ : W ⟶ T) (hδ : δ ≫ t = 𝟙 W) :
    IsPullback δ δ (pullback.lift (t ≫ δ) (𝟙 T) (by rw [Category.assoc, hδ]; simp))
      (pullback.diagonal t) := by
  have hw : δ ≫ pullback.lift (t ≫ δ) (𝟙 T) (by rw [Category.assoc, hδ]; simp) =
      δ ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        ← Category.assoc, hδ, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd]
  refine IsPullback.of_isLimit' ⟨hw⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun c ↦ c.snd ≫ t) (fun c ↦ ?_) (fun c ↦ ?_)
    (fun c m hm _ ↦ ?_)
  all_goals
    have h₁ := congrArg (· ≫ pullback.fst t t) c.condition
    have h₂ := congrArg (· ≫ pullback.snd t t) c.condition
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
      pullback.diagonal_fst, pullback.diagonal_snd] at h₁ h₂
  · rw [Category.assoc, ← h₂, h₁, h₂]
  · rw [Category.assoc, ← h₂, h₁, h₂]
  · rw [← h₂, ← hm, Category.assoc, hδ, Category.comp_id]

/-- **A section of an étale morphism of schemes is an open immersion.** It is a base change of
the diagonal, which is an open immersion for an unramified morphism locally of finite type. -/
@[ega "IV 17.9.3", sga "6 VIII 1.3" "more general"]
theorem isOpenImmersion_of_comp_eq_id_of_etale {T W : Scheme.{u}} (t : T ⟶ W) [Etale t]
    (δ : W ⟶ T) (hδ : δ ≫ t = 𝟙 W) : IsOpenImmersion δ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_section_diagonal t δ hδ).flip inferInstance

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the site out of the kernel pair of `p`, obtained from two morphisms with the
same image under `p`. -/
noncomputable def kernelPairLift {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Q : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X} {q₁ q₂ : Q ⟶ W}
    (hpb : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p) {Z : BigFppfOver B S hS}
    (a b : Z ⟶ W) (h : yoneda.map a ≫ p = yoneda.map b ≫ p) : Z ⟶ Q :=
  Yoneda.fullyFaithful.preimage (hpb.lift (yoneda.map a) (yoneda.map b) h)

/-- The lift `kernelPairLift a b h` composed with the first projection `q₁` is `a`. -/
@[reassoc (attr := simp)]
theorem kernelPairLift_fst {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Q : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X} {q₁ q₂ : Q ⟶ W}
    (hpb : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p) {Z : BigFppfOver B S hS}
    (a b : Z ⟶ W) (h : yoneda.map a ≫ p = yoneda.map b ≫ p) :
    kernelPairLift B S hS hpb a b h ≫ q₁ = a :=
  yoneda.map_injective (by simp [kernelPairLift])

/-- The lift `kernelPairLift a b h` composed with the second projection `q₂` is `b`. -/
@[reassoc (attr := simp)]
theorem kernelPairLift_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Q : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X} {q₁ q₂ : Q ⟶ W}
    (hpb : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p) {Z : BigFppfOver B S hS}
    (a b : Z ⟶ W) (h : yoneda.map a ≫ p = yoneda.map b ≫ p) :
    kernelPairLift B S hS hpb a b h ≫ q₂ = b :=
  yoneda.map_injective (by simp [kernelPairLift])

/-- The projections of a kernel pair are jointly monic in the site. -/
theorem kernelPair_hom_ext {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Q : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X} {q₁ q₂ : Q ⟶ W}
    (hpb : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p) {Z : BigFppfOver B S hS}
    (a b : Z ⟶ Q) (h₁ : a ≫ q₁ = b ≫ q₁) (h₂ : a ≫ q₂ = b ≫ q₂) : a = b :=
  yoneda.map_injective (hpb.hom_ext (by simp [← Functor.map_comp, h₁])
    (by simp [← Functor.map_comp, h₂]))

local notation "F" => BigFppfOver.toScheme B S hS

/-- The structure morphism of an object of the site, as a morphism of schemes to `S`. -/
def str (Z : BigFppfOver B S hS) : (F).obj Z ⟶ S := B.inclusion.map Z.hom

/-- The underlying morphism of schemes of a morphism of the site commutes with the structure
morphisms to `S`. -/
theorem map_comp_str {Z Z' : BigFppfOver B S hS} (f : Z ⟶ Z') :
    (F).map f ≫ str B S hS Z' = str B S hS Z := by
  have h := congrArg (fun g => B.inclusion.map g) (Over.w f)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact h

/-- **The kernel pair of a morphism from an object of the site is an equivalence relation of
schemes.** The kernel pair `q₁, q₂ : Q ⟶ W` of `p : W ⟶ X` is a kernel pair of presheaves on the
site; read on the underlying schemes it is an internal equivalence relation in the category of
all schemes. -/
@[sga "3 V 10.1.1"]
noncomputable def equivalenceRelation_kernel {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Q : BigFppfOver B S hS} {p : yoneda.obj W ⟶ X} {q₁ q₂ : Q ⟶ W}
    (hpb : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p) :
    EquivalenceRelation ((F).map q₁) ((F).map q₂) := by
  have hstr : (F).map q₁ ≫ str B S hS W = (F).map q₂ ≫ str B S hS W := by
    rw [map_comp_str, map_comp_str]
  -- joint monicity, tested on the universal object `Q ×_{W ×_S W} Q`
  let L : (F).obj Q ⟶ pullback (str B S hS W) (str B S hS W) := pullback.lift _ _ hstr
  have hL₁ : L ≫ pullback.fst _ _ = (F).map q₁ := pullback.lift_fst _ _ _
  have hL₂ : L ≫ pullback.snd _ _ = (F).map q₂ := pullback.lift_snd _ _ _
  clear_value L
  have hM : B.Contains (pullback L L) :=
    Scheme.size_pullback_lt L L Q.left.2 Q.left.2
  let M : BigFppfOver B S hS := BigFppfOver.mk B S hS hM (pullback.fst L L ≫ str B S hS Q)
  have hw₂ : pullback.snd L L ≫ str B S hS Q = pullback.fst L L ≫ str B S hS Q := by
    rw [← map_comp_str B S hS q₁, ← hL₁]
    simp only [← Category.assoc]
    rw [pullback.condition]
  let m₁ : M ⟶ Q := BigFppfOver.homMk B S hS Q.left.2 _ (pullback.fst L L) rfl
  let m₂ : M ⟶ Q := BigFppfOver.homMk B S hS Q.left.2 _ (pullback.snd L L) hw₂
  have e₁ : pullback.fst L L ≫ (F).map q₁ = pullback.snd L L ≫ (F).map q₁ := by
    rw [← hL₁, ← Category.assoc, pullback.condition, Category.assoc]
  have e₂ : pullback.fst L L ≫ (F).map q₂ = pullback.snd L L ≫ (F).map q₂ := by
    rw [← hL₂, ← Category.assoc, pullback.condition, Category.assoc]
  have hc₁ : m₁ ≫ q₁ = m₂ ≫ q₁ := BigFppfOver.map_toScheme_injective B S hS (by exact e₁)
  have hc₂ : m₁ ≫ q₂ = m₂ ≫ q₂ := BigFppfOver.map_toScheme_injective B S hS (by exact e₂)
  have hfs : pullback.fst L L = pullback.snd L L :=
    congrArg (fun a ↦ (F).map a) (kernelPair_hom_ext B S hS hpb m₁ m₂ hc₁ hc₂)
  -- the symmetry and the transitivity, from the universal property of the kernel pair
  let σ : Q ⟶ Q := kernelPairLift B S hS hpb q₂ q₁ hpb.w.symm
  have hP : B.Contains (pullback ((F).map q₂) ((F).map q₁)) :=
    Scheme.size_pullback_lt _ _ Q.left.2 Q.left.2
  let P : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hP (pullback.fst ((F).map q₂) ((F).map q₁) ≫ str B S hS Q)
  have hw₂' : pullback.snd ((F).map q₂) ((F).map q₁) ≫ str B S hS Q =
      pullback.fst ((F).map q₂) ((F).map q₁) ≫ str B S hS Q := by
    simpa only [Category.assoc, map_comp_str] using
      (pullback.condition (f := (F).map q₂) (g := (F).map q₁) =≫ str B S hS W).symm
  let c₁ : P ⟶ Q := BigFppfOver.homMk B S hS Q.left.2 _ (pullback.fst _ _) rfl
  let c₂ : P ⟶ Q := BigFppfOver.homMk B S hS Q.left.2 _ (pullback.snd _ _) hw₂'
  have hcc : c₁ ≫ q₂ = c₂ ≫ q₁ :=
    BigFppfOver.map_toScheme_injective B S hS (by exact pullback.condition)
  have hτ : yoneda.map (c₁ ≫ q₁) ≫ p = yoneda.map (c₂ ≫ q₂) ≫ p := by
    calc yoneda.map (c₁ ≫ q₁) ≫ p = yoneda.map c₁ ≫ yoneda.map q₂ ≫ p := by
          rw [yoneda.map_comp, Category.assoc, hpb.w]
      _ = yoneda.map c₂ ≫ yoneda.map q₁ ≫ p := by
          rw [← Category.assoc, ← yoneda.map_comp, hcc, yoneda.map_comp, Category.assoc]
      _ = yoneda.map (c₂ ≫ q₂) ≫ p := by
          rw [hpb.w, ← Category.assoc, ← yoneda.map_comp]
  let τ : P ⟶ Q := kernelPairLift B S hS hpb (c₁ ≫ q₁) (c₂ ≫ q₂) hτ
  let δ : W ⟶ Q := kernelPairLift B S hS hpb (𝟙 W) (𝟙 W) rfl
  have hr₁ : (F).map δ ≫ (F).map q₁ = 𝟙 _ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_fst B S hS hpb (𝟙 W) (𝟙 W) rfl)
    exact this
  have hr₂ : (F).map δ ≫ (F).map q₂ = 𝟙 _ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_snd B S hS hpb (𝟙 W) (𝟙 W) rfl)
    exact this
  have hs₁ : (F).map σ ≫ (F).map q₁ = (F).map q₂ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_fst B S hS hpb q₂ q₁ hpb.w.symm)
    exact this
  have hs₂ : (F).map σ ≫ (F).map q₂ = (F).map q₁ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_snd B S hS hpb q₂ q₁ hpb.w.symm)
    exact this
  have ht₁ : (F).map τ ≫ (F).map q₁ = pullback.fst ((F).map q₂) ((F).map q₁) ≫ (F).map q₁ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_fst B S hS hpb _ _ hτ)
    exact this
  have ht₂ : (F).map τ ≫ (F).map q₂ = pullback.snd ((F).map q₂) ((F).map q₁) ≫ (F).map q₂ := by
    have := congrArg (fun a ↦ (F).map a) (kernelPairLift_snd B S hS hpb _ _ hτ)
    exact this
  exact
    { right_cancellation := fun Y f g h₁ h₂ ↦ by
        have hfg : f ≫ L = g ≫ L := pullback.hom_ext
          (by rw [Category.assoc, Category.assoc, hL₁, h₁])
          (by rw [Category.assoc, Category.assoc, hL₂, h₂])
        rw [← pullback.lift_fst f g hfg, hfs, pullback.lift_snd]
      r := (F).map δ
      reflexivity₁ := hr₁
      reflexivity₂ := hr₂
      s := (F).map σ
      symmetry₁ := hs₁
      symmetry₂ := hs₂
      c := pullback.cone _ _
      isLimit := pullback.isLimit _ _
      t := (F).map τ
      transitivity₁ := ht₁
      transitivity₂ := ht₂ }

/-- **The data of the extended relation.** An open immersion `j : W ⟶ V` of objects of the site,
a morphism `p : W ⟶ X` to a presheaf, a representing kernel pair `q₁, q₂ : Q ⟶ W` of `p` whose
projections are étale morphisms of schemes. -/
structure OpenKernelPairExtension (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (V W : BigFppfOver B S hS) where
  /-- The open immersion of the chart. -/
  j : W ⟶ V
  /-- The morphism `j` is an open immersion of schemes. -/
  isOpenImmersion_j : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)
  /-- The morphism whose kernel pair is glued in. -/
  p : yoneda.obj W ⟶ X
  /-- The object representing the kernel pair. -/
  Q : BigFppfOver B S hS
  /-- The first projection of the kernel pair. -/
  q₁ : Q ⟶ W
  /-- The second projection of the kernel pair. -/
  q₂ : Q ⟶ W
  /-- `q₁, q₂` form a kernel pair of `p`. -/
  isPullback : IsPullback (yoneda.map q₁) (yoneda.map q₂) p p
  /-- The first projection of the kernel pair is étale. -/
  etale_q₁ : Etale ((BigFppfOver.toScheme B S hS).map q₁)
  /-- The second projection of the kernel pair is étale. -/
  etale_q₂ : Etale ((BigFppfOver.toScheme B S hS).map q₂)

namespace OpenKernelPairExtension

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : BigFppfOver B S hS}
  (E : OpenKernelPairExtension B S hS X V W)

attribute [instance] isOpenImmersion_j etale_q₁ etale_q₂

/-- The diagonal of the kernel pair. -/
noncomputable def δ : W ⟶ E.Q := kernelPairLift B S hS E.isPullback (𝟙 W) (𝟙 W) rfl

/-- The diagonal composed with the first projection is the identity of `W`. -/
@[reassoc (attr := simp)]
theorem δ_q₁ : E.δ ≫ E.q₁ = 𝟙 W := kernelPairLift_fst _ _ _ _ _ _ _

/-- The diagonal composed with the second projection is the identity of `W`. -/
@[reassoc (attr := simp)]
theorem δ_q₂ : E.δ ≫ E.q₂ = 𝟙 W := kernelPairLift_snd _ _ _ _ _ _ _

/-- On underlying schemes, the diagonal composed with the first projection is the identity. -/
theorem map_δ_q₁ : (F).map E.δ ≫ (F).map E.q₁ = 𝟙 _ := by
  rw [← (F).map_comp, δ_q₁, (F).map_id]

/-- On underlying schemes, the diagonal composed with the second projection is the identity. -/
theorem map_δ_q₂ : (F).map E.δ ≫ (F).map E.q₂ = 𝟙 _ := by
  rw [← (F).map_comp, δ_q₂, (F).map_id]

/-- The diagonal of the kernel pair is an open immersion, being a section of an étale
morphism. -/
instance isOpenImmersion_δ : AlgebraicGeometry.IsOpenImmersion ((F).map E.δ) :=
  isOpenImmersion_of_comp_eq_id_of_etale _ _ E.map_δ_q₁

/-- The glued scheme `V ⊔_W Q`. -/
noncomputable abbrev glued : Scheme.{u} := pushout ((F).map E.j) ((F).map E.δ)

/-- The target map of the glued relation, on schemes. -/
noncomputable abbrev targetScheme : E.glued ⟶ (F).obj V :=
  RelationExtension.target ((F).map E.j) ((F).map E.q₁) ((F).map E.δ) E.map_δ_q₁

/-- The source map of the glued relation, on schemes. -/
noncomputable abbrev sourceScheme : E.glued ⟶ (F).obj V :=
  RelationExtension.source ((F).map E.j) ((F).map E.q₂) ((F).map E.δ) E.map_δ_q₂

/-- The target and source maps of the glued scheme agree after composing with the structure
morphism of `V` to `S`. -/
theorem targetScheme_str : E.targetScheme ≫ str B S hS V = E.sourceScheme ≫ str B S hS V := by
  refine pushout.hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, RelationExtension.inl_target,
      RelationExtension.inl_source]
  · rw [← Category.assoc, ← Category.assoc, RelationExtension.inr_target,
      RelationExtension.inr_source, Category.assoc, Category.assoc, map_comp_str, map_comp_str,
      map_comp_str]

/-- The glued scheme lies in the site: it is covered by two opens isomorphic to `V` and `Q`. -/
theorem contains_glued : B.Contains E.glued := by
  have hcov : (⨆ b : ULift.{u} Bool, if b.down then (pushout.inl ((F).map E.j)
      ((F).map E.δ)).opensRange else (pushout.inr ((F).map E.j) ((F).map E.δ)).opensRange) =
        ⊤ := by
    rw [← RelationExtension.iSup_opensRange_eq_top (j := (F).map E.j) (δ := (F).map E.δ)]
    apply le_antisymm
    · exact iSup_le fun b ↦ by cases b with | up b => cases b <;> simp
    · exact sup_le (le_iSup_of_le ⟨true⟩ (by simp)) (le_iSup_of_le ⟨false⟩ (by simp))
  refine (Scheme.size_le_of_iSup_eq_top _ hcov).trans_lt (max_lt ?_ ?_)
  · exact (Cardinal.mk_le_aleph0).trans_lt B.aleph0_lt_cutoff
  · refine (ciSup_le' fun b ↦ ?_).trans_lt (max_lt V.left.2 E.Q.left.2)
    cases b with
    | up b =>
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [← Scheme.size_congr (pushout.inr ((F).map E.j) ((F).map E.δ)).isoOpensRange]
        exact le_max_right _ _
      · simp only [if_true]
        rw [← Scheme.size_congr (pushout.inl ((F).map E.j) ((F).map E.δ)).isoOpensRange]
        exact le_max_left _ _

/-- The glued relation `R = V ⊔_W Q`, as an object of the site, over `S` through `V`. -/
noncomputable def R : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS E.contains_glued (E.targetScheme ≫ str B S hS V)

/-- The target morphism `R ⟶ V`: the identity on `V` and `q₁ ≫ j` on `Q`. -/
noncomputable def t : E.R ⟶ V := BigFppfOver.homMk B S hS V.left.2 _ E.targetScheme rfl

/-- The source morphism `R ⟶ V`: the identity on `V` and `q₂ ≫ j` on `Q`. -/
noncomputable def s : E.R ⟶ V :=
  BigFppfOver.homMk B S hS V.left.2 _ E.sourceScheme E.targetScheme_str.symm

/-- The chart `V ⟶ R`. -/
noncomputable def inl : V ⟶ E.R :=
  BigFppfOver.homMk B S hS E.contains_glued _ (pushout.inl _ _) (by
    rw [← Category.assoc, RelationExtension.inl_target, Category.id_comp]
    rfl)

/-- The chart `Q ⟶ R`. -/
noncomputable def inr : E.Q ⟶ E.R :=
  BigFppfOver.homMk B S hS E.contains_glued _ (pushout.inr _ _) (by
    rw [← Category.assoc, RelationExtension.inr_target, Category.assoc, map_comp_str,
      map_comp_str]
    rfl)

/-- The underlying morphism of schemes of `t` is `targetScheme`. -/
theorem map_t : (F).map E.t = E.targetScheme := rfl

/-- The underlying morphism of schemes of `s` is `sourceScheme`. -/
theorem map_s : (F).map E.s = E.sourceScheme := rfl

/-- The underlying morphism of schemes of `inl` is the pushout inclusion of `V`. -/
theorem map_inl : (F).map E.inl = pushout.inl _ _ := rfl

/-- The underlying morphism of schemes of `inr` is the pushout inclusion of `Q`. -/
theorem map_inr : (F).map E.inr = pushout.inr _ _ := rfl

/-- The target morphism restricts to the identity on the chart `V`. -/
@[reassoc (attr := simp)]
theorem inl_t : E.inl ≫ E.t = 𝟙 V :=
  BigFppfOver.map_toScheme_injective B S hS (by
    exact RelationExtension.inl_target (j := (F).map E.j) E.map_δ_q₁)

/-- The source morphism restricts to the identity on the chart `V`. -/
@[reassoc (attr := simp)]
theorem inl_s : E.inl ≫ E.s = 𝟙 V :=
  BigFppfOver.map_toScheme_injective B S hS (by
    exact RelationExtension.inl_source (j := (F).map E.j) E.map_δ_q₂)

/-- The target morphism restricts to `q₁ ≫ j` on the chart `Q`. -/
@[reassoc (attr := simp)]
theorem inr_t : E.inr ≫ E.t = E.q₁ ≫ E.j :=
  BigFppfOver.map_toScheme_injective B S hS (by
    exact RelationExtension.inr_target (j := (F).map E.j) E.map_δ_q₁)

/-- The source morphism restricts to `q₂ ≫ j` on the chart `Q`. -/
@[reassoc (attr := simp)]
theorem inr_s : E.inr ≫ E.s = E.q₂ ≫ E.j :=
  BigFppfOver.map_toScheme_injective B S hS (by
    exact RelationExtension.inr_source (j := (F).map E.j) E.map_δ_q₂)

/-- On underlying schemes, the charts `inl` and `inr` exhibit `R` as the pushout of `j` and the
diagonal `δ`. -/
theorem isPushout_map : IsPushout ((F).map E.j) ((F).map E.δ) ((F).map E.inl) ((F).map E.inr) :=
  IsPushout.of_hasPushout _ _

/-- **The glued relation is an étale equivalence relation over `S`.** -/
theorem isEtaleEquivalenceRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS E.s E.t) := by
  have hQ : IsEquivalenceRelation ((F).map E.q₁) ((F).map E.q₂) :=
    (equivalenceRelation_kernel B S hS E.isPullback).isEquivalenceRelation
  have hR : IsEquivalenceRelation E.targetScheme E.sourceScheme :=
    RelationExtension.isEquivalenceRelation (j := (F).map E.j) (δ := (F).map E.δ)
      E.map_δ_q₁ E.map_δ_q₂
  have htarget : (relation B S hS E.s E.t).target = (Over.post B.inclusion).map E.t := by
    show prod.lift _ _ ≫ prod.fst = _
    exact prod.lift_fst _ _
  have hsource : (relation B S hS E.s E.t).source = (Over.post B.inclusion).map E.s := by
    show prod.lift _ _ ≫ prod.snd = _
    exact prod.lift_snd _ _
  have : IsEquivalenceRelation (relation B S hS E.s E.t).target
      (relation B S hS E.s E.t).source :=
    Stacks.Groupoids.isEquivalenceRelation_of_iso_left _ (Iso.refl _) E.targetScheme
      E.sourceScheme (by rw [htarget]; exact Category.id_comp _)
      (by rw [hsource]; exact Category.id_comp _) hR
  have : Etale (relation B S hS E.s E.t).source.left := by
    rw [hsource]
    exact RelationExtension.etale_source (j := (F).map E.j) (δ := (F).map E.δ) E.map_δ_q₂
  have : Etale (relation B S hS E.s E.t).target.left := by
    rw [htarget]
    exact RelationExtension.etale_target (j := (F).map E.j) (δ := (F).map E.δ) E.map_δ_q₁
  exact ⟨⟩

end OpenKernelPairExtension

end Space

end AlgebraicGeometry

end
