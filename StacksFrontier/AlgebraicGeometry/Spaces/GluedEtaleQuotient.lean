module

public import StacksFrontier.AlgebraicGeometry.Spaces.GluedEtaleEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleDescentAlongPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientOfCartesianRelation
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful

/-!
# The quotient by a glued étale equivalence relation

Let `U` be an algebraic space, `j : Y ⟶ V` an open immersion of objects of the big fppf site
and `y : Y ⟶ U` an étale morphism, and let `Q = Y ×_U Y`. Glueing `V` to `Q` along the diagonal
copy of `Y` gives an étale equivalence relation `R ⇉ V`
(`AlgebraicGeometry.GluedRelation`); its quotient `V / R` is an algebraic space (Stacks 02WW).

## Main definitions

* `AlgebraicGeometry.Space.GluedEtaleDatum`: the data `(U, V, Y, j, y, Q)`.
* `AlgebraicGeometry.Space.GluedEtaleDatum.relation`, `.src`, `.tgt`: the glued relation as an
  object of the site with its two projections.
* `AlgebraicGeometry.Space.GluedEtaleDatum.quotient`: the quotient algebraic space.

## Main results

* `AlgebraicGeometry.Space.GluedEtaleDatum.isEtaleEquivalenceRelation`: the glued relation is an
  étale equivalence relation.
* `AlgebraicGeometry.Space.GluedEtaleDatum.isPullback_quotientMap`: the glued relation is the
  kernel pair of the quotient map.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The data of a glued étale relation: an open immersion `j : Y ⟶ V` of objects of the site, an
étale morphism `y : Y ⟶ U` to an algebraic space, and the fibre product `Q = Y ×_U Y`. -/
structure GluedEtaleDatum where
  /-- The algebraic space. -/
  U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  isAlgebraicSpace_U : IsAlgebraicSpace B S hS U
  /-- The scheme to be glued. -/
  V : BigFppfOver B S hS
  /-- Its open subscheme. -/
  Y : BigFppfOver B S hS
  /-- The open immersion. -/
  j : Y ⟶ V
  [isOpenImmersion_j :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
  /-- The étale morphism to the algebraic space. -/
  y : yoneda.obj Y ⟶ U
  isEtale_y : IsEtale B S hS y
  /-- The fibre product `Y ×_U Y`. -/
  Q : BigFppfOver B S hS
  /-- Its first projection. -/
  p₁ : Q ⟶ Y
  /-- Its second projection. -/
  p₂ : Q ⟶ Y
  isPullback_Q : IsPullback (yoneda.map p₁) (yoneda.map p₂) y y
  [compactSpace_V : CompactSpace ((BigFppfOver.toScheme B S hS).obj V)]
  [compactSpace_Q : CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)]

/-- **A pair of morphisms of the site which is jointly monic for test objects of the site is
jointly monic as a pair of morphisms of schemes**, for test morphisms from arbitrary schemes. -/
theorem toScheme_jointlyMono {Q Y₁ Y₂ : BigFppfOver B S hS} (p₁ : Q ⟶ Y₁) (p₂ : Q ⟶ Y₂)
    (h : ∀ {T : BigFppfOver B S hS} (x y : T ⟶ Q), x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y)
    {Z : Scheme.{u}} (x y : Z ⟶ (BigFppfOver.toScheme B S hS).obj Q)
    (h₁ : x ≫ (BigFppfOver.toScheme B S hS).map p₁ = y ≫ (BigFppfOver.toScheme B S hS).map p₁)
    (h₂ : x ≫ (BigFppfOver.toScheme B S hS).map p₂ = y ≫ (BigFppfOver.toScheme B S hS).map p₂) :
    x = y := by
  let G := BigFppfOver.toScheme B S hS
  have : HasTerminal (BigFppfOver B S hS) := (Over.mkIdTerminal (X := B.obj hS)).hasTerminal
  have : HasBinaryProducts (BigFppfOver B S hS) := hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let m : Q ⟶ Y₁ ⨯ Y₂ := prod.lift p₁ p₂
  have hm : Mono m := ⟨fun f g hfg => h f g (by simpa [m] using congrArg (· ≫ prod.fst) hfg)
    (by simpa [m] using congrArg (· ≫ prod.snd) hfg)⟩
  have : Mono (G.map m) := inferInstance
  have hP := (IsPullback.of_hasBinaryProduct' (C := BigFppfOver B S hS) Y₁ Y₂).map G
  refine (cancel_mono (G.map m)).1 (hP.hom_ext ?_ ?_)
  · simpa only [Category.assoc, ← G.map_comp, m, prod.lift_fst] using h₁
  · simpa only [Category.assoc, ← G.map_comp, m, prod.lift_snd] using h₂

/-- A pair of morphisms of the site jointly monic on representable presheaves is jointly monic on
presheaves. -/
theorem jointlyMono₂_yoneda {Q Y₁ Y₂ : BigFppfOver B S hS} (p₁ : Q ⟶ Y₁) (p₂ : Q ⟶ Y₂)
    (h : ∀ {T : BigFppfOver B S hS} (x y : T ⟶ Q), x ≫ p₁ = y ≫ p₁ → x ≫ p₂ = y ≫ p₂ → x = y) :
    JointlyMono₂ (yoneda.map p₁) (yoneda.map p₂) where
  right_cancellation _ f g h₁ h₂ := by
    ext T z
    exact h (f.app T z) (g.app T z) (congrFun (congrArg (fun α => α.app T) h₁) z)
      (congrFun (congrArg (fun α => α.app T) h₂) z)

namespace GluedEtaleDatum

attribute [instance] isOpenImmersion_j compactSpace_V compactSpace_Q

variable {B S hS} (D : GluedEtaleDatum B S hS)

local notation "𝕋" => BigFppfOver.toScheme B S hS

/-- The diagonal of `Q`. -/
noncomputable def d : D.Y ⟶ D.Q := yoneda.preimage (D.isPullback_Q.lift (𝟙 _) (𝟙 _) rfl)

/-- The diagonal of `Q` is a section of the first projection. -/
@[reassoc (attr := simp)]
theorem d_p₁ : D.d ≫ D.p₁ = 𝟙 _ := yoneda.map_injective (by simp [d])

/-- The diagonal of `Q` is a section of the second projection. -/
@[reassoc (attr := simp)]
theorem d_p₂ : D.d ≫ D.p₂ = 𝟙 _ := yoneda.map_injective (by simp [d])

/-- The first projection `Q ⟶ Y` is étale. -/
theorem etale_p₁ : Etale ((𝕋).map D.p₁) :=
  (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mp
    (presheaf_of_isPullback B S hS D.isPullback_Q.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS D.y).mp D.isEtale_y))

/-- The second projection `Q ⟶ Y` is étale. -/
theorem etale_p₂ : Etale ((𝕋).map D.p₂) :=
  (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mp
    (presheaf_of_isPullback B S hS D.isPullback_Q
      ((isEtale_iff_presheaf_of_yoneda B S hS D.y).mp D.isEtale_y))

/-- The diagonal `Y ⟶ Q` is an open immersion of schemes. -/
instance isOpenImmersion_d : _root_.AlgebraicGeometry.IsOpenImmersion ((𝕋).map D.d) := by
  have := D.etale_p₁
  exact isOpenImmersion_of_section_of_etale ((𝕋).map D.p₁) ((𝕋).map D.d)
    (by rw [← Functor.map_comp, d_p₁, CategoryTheory.Functor.map_id])

/-- On underlying schemes, the diagonal of `Q` is a section of the first projection. -/
theorem hd₁ : (𝕋).map D.d ≫ (𝕋).map D.p₁ = 𝟙 _ := by
  rw [← Functor.map_comp, d_p₁, CategoryTheory.Functor.map_id]

/-- On underlying schemes, the diagonal of `Q` is a section of the second projection. -/
theorem hd₂ : (𝕋).map D.d ≫ (𝕋).map D.p₂ = 𝟙 _ := by
  rw [← Functor.map_comp, d_p₂, CategoryTheory.Functor.map_id]

/-- The glued scheme, as a scheme. -/
noncomputable abbrev relationScheme : Scheme.{u} := pushout ((𝕋).map D.j) ((𝕋).map D.d)

/-- The chart `V` of the glued scheme. -/
noncomputable abbrev a : (𝕋).obj D.V ⟶ D.relationScheme := pushout.inl _ _

/-- The chart `Q` of the glued scheme. -/
noncomputable abbrev b : (𝕋).obj D.Q ⟶ D.relationScheme := pushout.inr _ _

/-- The glued scheme is the pushout of `j : Y ⟶ V` and the diagonal `Y ⟶ Q`. -/
theorem isPushout : IsPushout ((𝕋).map D.j) ((𝕋).map D.d) D.a D.b := IsPushout.of_hasPushout _ _

/-- The first projection of the glued relation, as a morphism of schemes. -/
noncomputable abbrev src₀ : D.relationScheme ⟶ (𝕋).obj D.V :=
  GluedRelation.src (j := (𝕋).map D.j) (p₁ := (𝕋).map D.p₁) D.hd₁ D.isPushout

/-- The second projection of the glued relation, as a morphism of schemes. -/
noncomputable abbrev tgt₀ : D.relationScheme ⟶ (𝕋).obj D.V :=
  GluedRelation.tgt (j := (𝕋).map D.j) (p₂ := (𝕋).map D.p₂) D.hd₂ D.isPushout

/-- Étale morphisms of schemes are Zariski-local at the source. -/
private instance isZariskiLocalAtSource_etale : IsZariskiLocalAtSource (@Etale.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)

/-- The first projection of the glued relation is étale. -/
theorem etale_src₀ : Etale D.src₀ := by
  have := D.etale_p₁
  exact GluedRelation.src_of_isZariskiLocalAtSource D.hd₁ D.isPushout @Etale inferInstance
    inferInstance

/-- The second projection of the glued relation is étale. -/
theorem etale_tgt₀ : Etale D.tgt₀ := by
  have := D.etale_p₂
  exact GluedRelation.tgt_of_isZariskiLocalAtSource D.hd₂ D.isPushout @Etale inferInstance
    inferInstance

/-- The glued scheme is quasi-compact. -/
instance compactSpace_relationScheme : CompactSpace D.relationScheme :=
  GluedRelation.compactSpace D.isPushout

/-- The first projection of the glued relation is locally of finite type. -/
instance locallyOfFiniteType_src₀ : LocallyOfFiniteType D.src₀ := by
  have := D.etale_src₀
  infer_instance

/-- The glued relation, as an object of the site. -/
noncomputable abbrev relation : BigFppfOver B S hS := siteObjectOfLocallyOfFiniteType D.V D.src₀

/-- The first projection of the glued relation. -/
noncomputable abbrev src : D.relation ⟶ D.V := siteObjectOfLocallyOfFiniteType.hom D.V D.src₀

/-- The two projections of the glued relation agree after composing with the structure morphism
of `V`. -/
theorem tgt₀_hom : D.tgt₀ ≫ D.V.hom.hom = D.src₀ ≫ D.V.hom.hom := by
  refine D.isPushout.hom_ext ?_ ?_
  · rw [GluedRelation.a_tgt_assoc, GluedRelation.a_src_assoc]
  · rw [GluedRelation.b_tgt_assoc, GluedRelation.b_src_assoc]
    have hj : (𝕋).map D.j ≫ D.V.hom.hom = D.Y.hom.hom := congrArg (fun f => f.hom) (Over.w D.j)
    have h₁ : (𝕋).map D.p₁ ≫ D.Y.hom.hom = D.Q.hom.hom := congrArg (fun f => f.hom) (Over.w D.p₁)
    have h₂ : (𝕋).map D.p₂ ≫ D.Y.hom.hom = D.Q.hom.hom := congrArg (fun f => f.hom) (Over.w D.p₂)
    rw [hj, h₁, h₂]

/-- The second projection of the glued relation. -/
noncomputable def tgt : D.relation ⟶ D.V :=
  Over.homMk (ObjectProperty.homMk D.tgt₀) (by ext1; exact D.tgt₀_hom)

/-- The underlying morphism of schemes of `src` is `src₀`. -/
@[simp] theorem toScheme_map_src : (𝕋).map D.src = D.src₀ := rfl

/-- The underlying morphism of schemes of `tgt` is `tgt₀`. -/
@[simp] theorem toScheme_map_tgt : (𝕋).map D.tgt = D.tgt₀ := rfl

/-- Two morphisms into `Q` from an object of the site agree if they agree after both
projections. -/
theorem Q_hom_ext {T : BigFppfOver B S hS} (x y : T ⟶ D.Q) (h₁ : x ≫ D.p₁ = y ≫ D.p₁)
    (h₂ : x ≫ D.p₂ = y ≫ D.p₂) : x = y :=
  yoneda.map_injective (D.isPullback_Q.hom_ext (by simpa using congrArg yoneda.map h₁)
    (by simpa using congrArg yoneda.map h₂))

/-- Two morphisms of schemes into `Q` agree if they agree after both projections. -/
theorem Q_scheme_hom_ext {T : Scheme.{u}} (x y : T ⟶ (𝕋).obj D.Q)
    (h₁ : x ≫ (𝕋).map D.p₁ = y ≫ (𝕋).map D.p₁) (h₂ : x ≫ (𝕋).map D.p₂ = y ≫ (𝕋).map D.p₂) :
    x = y :=
  toScheme_jointlyMono B S hS D.p₁ D.p₂ D.Q_hom_ext x y h₁ h₂

/-- The symmetry of `Q`. -/
noncomputable def symmQ : D.Q ⟶ D.Q :=
  yoneda.preimage (D.isPullback_Q.lift (yoneda.map D.p₂) (yoneda.map D.p₁) D.isPullback_Q.w.symm)

/-- The symmetry of `Q` followed by the first projection is the second projection. -/
@[reassoc (attr := simp)]
theorem symmQ_p₁ : D.symmQ ≫ D.p₁ = D.p₂ := yoneda.map_injective (by simp [symmQ])

/-- The symmetry of `Q` followed by the second projection is the first projection. -/
@[reassoc (attr := simp)]
theorem symmQ_p₂ : D.symmQ ≫ D.p₂ = D.p₁ := yoneda.map_injective (by simp [symmQ])

/-- The composition of `Q`. -/
noncomputable def transQ : pullback D.p₂ D.p₁ ⟶ D.Q :=
  yoneda.preimage (D.isPullback_Q.lift (yoneda.map (pullback.fst _ _ ≫ D.p₁))
    (yoneda.map (pullback.snd _ _ ≫ D.p₂)) (by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, D.isPullback_Q.w,
        ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        D.isPullback_Q.w]))

/-- The first projection of a composite in `Q` is the first projection of its first factor. -/
@[reassoc (attr := simp)]
theorem transQ_p₁ : D.transQ ≫ D.p₁ = pullback.fst _ _ ≫ D.p₁ :=
  yoneda.map_injective (by simp [transQ])

/-- The second projection of a composite in `Q` is the second projection of its second factor. -/
@[reassoc (attr := simp)]
theorem transQ_p₂ : D.transQ ≫ D.p₂ = pullback.snd _ _ ≫ D.p₂ :=
  yoneda.map_injective (by simp [transQ])

/-- `Q` is transitive on `T`-points for every scheme `T`: if `x ≫ p₂ = y ≫ p₁`, there is a point
`z` of `Q` with `z ≫ p₁ = x ≫ p₁` and `z ≫ p₂ = y ≫ p₂`. -/
theorem Q_scheme_trans {T : Scheme.{u}} (x y : T ⟶ (𝕋).obj D.Q)
    (h : x ≫ (𝕋).map D.p₂ = y ≫ (𝕋).map D.p₁) :
    ∃ z : T ⟶ (𝕋).obj D.Q, z ≫ (𝕋).map D.p₁ = x ≫ (𝕋).map D.p₁ ∧
      z ≫ (𝕋).map D.p₂ = y ≫ (𝕋).map D.p₂ := by
  let e := PreservesPullback.iso (𝕋) D.p₂ D.p₁
  refine ⟨pullback.lift x y h ≫ e.inv ≫ (𝕋).map D.transQ, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← Functor.map_comp, transQ_p₁, Functor.map_comp,
      ← Category.assoc e.inv, PreservesPullback.iso_inv_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, Category.assoc, ← Functor.map_comp, transQ_p₂, Functor.map_comp,
      ← Category.assoc e.inv, PreservesPullback.iso_inv_snd, pullback.lift_snd_assoc]

/-- The two projections of the glued relation are jointly monic, for test morphisms from
arbitrary schemes. -/
theorem relation_scheme_hom_ext {T : Scheme.{u}} (x y : T ⟶ D.relationScheme)
    (h₁ : x ≫ D.src₀ = y ≫ D.src₀) (h₂ : x ≫ D.tgt₀ = y ≫ D.tgt₀) : x = y :=
  GluedRelation.hom_ext_of_isPushout D.hd₁ D.hd₂ D.isPushout
    D.Q_scheme_hom_ext h₁ h₂

/-- The two projections of the glued relation are jointly monic in the site. -/
theorem relation_hom_ext {T : BigFppfOver B S hS} (x y : T ⟶ D.relation)
    (h₁ : x ≫ D.src = y ≫ D.src) (h₂ : x ≫ D.tgt = y ≫ D.tgt) : x = y :=
  (𝕋).map_injective (D.relation_scheme_hom_ext _ _
    (by have h := congrArg (𝕋).map h₁; simp only [Functor.map_comp] at h; exact h)
    (by have h := congrArg (𝕋).map h₂; simp only [Functor.map_comp] at h; exact h))

/-- The glued relation is an equivalence relation of represented presheaves. -/
theorem isEquivalenceRelation :
    IsEquivalenceRelation (yoneda.map D.src) (yoneda.map D.tgt) := by
  have hjm := jointlyMono₂_yoneda B S hS D.src D.tgt D.relation_hom_ext
  let r : D.V ⟶ D.relation := siteObjectOfLocallyOfFiniteType.lift D.V D.src₀ D.a (by
    rw [GluedRelation.a_src_assoc])
  have hr₁ : r ≫ D.src = 𝟙 _ := (𝕋).map_injective (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact GluedRelation.a_src D.hd₁ D.isPushout)
  have hr₂ : r ≫ D.tgt = 𝟙 _ := (𝕋).map_injective (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact GluedRelation.a_tgt D.hd₂ D.isPushout)
  obtain ⟨σ, hσ₁, hσ₂⟩ := GluedRelation.exists_symm D.hd₁ D.hd₂ D.isPushout
    D.Q_scheme_hom_ext ((𝕋).map D.symmQ)
    (by rw [← Functor.map_comp, symmQ_p₁]) (by rw [← Functor.map_comp, symmQ_p₂])
  let σs : D.relation ⟶ D.relation := siteObjectOfLocallyOfFiniteType.lift D.V D.src₀ σ (by
    change D.src₀ ≫ D.V.hom.hom = σ ≫ D.src₀ ≫ D.V.hom.hom
    rw [← Category.assoc, hσ₁, D.tgt₀_hom])
  have hσ₁s : σs ≫ D.src = D.tgt := (𝕋).map_injective (by rw [Functor.map_comp]; exact hσ₁)
  have hσ₂s : σs ≫ D.tgt = D.src := (𝕋).map_injective (by rw [Functor.map_comp]; exact hσ₂)
  obtain ⟨τ, hτ₁, hτ₂⟩ := GluedRelation.exists_trans D.hd₁ D.hd₂ D.isPushout
    D.Q_scheme_hom_ext D.Q_scheme_trans
  let φ : (𝕋).obj (pullback D.tgt D.src) ⟶ pullback D.tgt₀ D.src₀ :=
    pullback.lift ((𝕋).map (pullback.fst D.tgt D.src)) ((𝕋).map (pullback.snd D.tgt D.src)) (by
      change (𝕋).map _ ≫ (𝕋).map D.tgt = (𝕋).map _ ≫ (𝕋).map D.src
      rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hφ₁ : φ ≫ pullback.fst D.tgt₀ D.src₀ = (𝕋).map (pullback.fst D.tgt D.src) :=
    pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd D.tgt₀ D.src₀ = (𝕋).map (pullback.snd D.tgt D.src) :=
    pullback.lift_snd _ _ _
  let τs : pullback D.tgt D.src ⟶ D.relation := siteObjectOfLocallyOfFiniteType.lift D.V D.src₀
    (φ ≫ τ) (by
      have hw : (pullback D.tgt D.src).hom.hom =
          (𝕋).map (pullback.fst D.tgt D.src) ≫ D.relation.hom.hom :=
        (congrArg (fun f => f.hom) (Over.w (pullback.fst D.tgt D.src))).symm
      rw [hw, Category.assoc, ← Category.assoc τ, hτ₁, Category.assoc, ← Category.assoc φ, hφ₁]
      rfl)
  have hτ₁s : τs ≫ D.src = pullback.fst _ _ ≫ D.src := (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    change (φ ≫ τ) ≫ D.src₀ = _
    rw [Category.assoc, hτ₁, ← Category.assoc, hφ₁]
    rfl)
  have hτ₂s : τs ≫ D.tgt = pullback.snd _ _ ≫ D.tgt := (𝕋).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    change (φ ≫ τ) ≫ D.tgt₀ = _
    rw [Category.assoc, hτ₂, ← Category.assoc, hφ₂]
    rfl)
  have hP := (IsPullback.of_hasPullback D.tgt D.src).map yoneda
  exact ⟨⟨{ toJointlyMono₂ := hjm,
            r := yoneda.map r,
            reflexivity₁ := by rw [← Functor.map_comp, hr₁, CategoryTheory.Functor.map_id],
            reflexivity₂ := by rw [← Functor.map_comp, hr₂, CategoryTheory.Functor.map_id],
            s := yoneda.map σs,
            symmetry₁ := by rw [← Functor.map_comp, hσ₁s],
            symmetry₂ := by rw [← Functor.map_comp, hσ₂s],
            c := hP.cone,
            isLimit := hP.isLimit,
            t := yoneda.map τs,
            transitivity₁ := by
              change yoneda.map τs ≫ yoneda.map D.src =
                yoneda.map (pullback.fst D.tgt D.src) ≫ yoneda.map D.src
              rw [← Functor.map_comp, hτ₁s, Functor.map_comp],
            transitivity₂ := by
              change yoneda.map τs ≫ yoneda.map D.tgt =
                yoneda.map (pullback.snd D.tgt D.src) ≫ yoneda.map D.tgt
              rw [← Functor.map_comp, hτ₂s, Functor.map_comp] }⟩⟩

instance isEtaleEquivalenceRelation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS D.tgt D.src) :=
  isEtaleEquivalenceRelation_of_yoneda B S hS D.tgt D.src (Iso.refl _)
    (by simpa using D.isEquivalenceRelation) D.etale_src₀ D.etale_tgt₀

/-- **The quotient of `V` by the glued relation** (Stacks 02WW). -/
noncomputable abbrev quotient : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (Space.relation B S hS D.tgt D.src)).obj

/-- The quotient map. -/
noncomputable abbrev quotientMap : yoneda.obj D.V ⟶ D.quotient :=
  Space.quotientMap B S hS D.tgt D.src

/-- The quotient of `V` by the glued relation is an algebraic space. -/
theorem isAlgebraicSpace_quotient : IsAlgebraicSpace B S hS D.quotient :=
  isAlgebraicSpace_quotient_unconditional B S hS D.tgt D.src

/-- The quotient map `V ⟶ V / R` is surjective. -/
theorem surjective_quotientMap :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf D.quotientMap :=
  quotientMap_surjective_unconditional B S hS D.tgt D.src

/-- The quotient map `V ⟶ V / R` is étale. -/
theorem etale_quotientMap :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf D.quotientMap :=
  quotientMap_etale_unconditional B S hS D.tgt D.src

/-- **The glued relation is the kernel pair of the quotient map.** -/
theorem isPullback_quotientMap :
    IsPullback (yoneda.map D.src) (yoneda.map D.tgt) D.quotientMap D.quotientMap :=
  Space.quotientMap_isPullback B S hS D.tgt D.src

end GluedEtaleDatum

end AlgebraicGeometry.Space

end
