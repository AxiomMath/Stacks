module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Statement
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The class at infinity is unchanged by a proper modification (Stacks 0FAQ)

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let `g : W' ⟶ W` be proper and an
isomorphism over `𝐀¹_X`, that is, over the open `b⁻¹(𝐀¹_X) ⊆ W`. Then `b' = b ∘ g` is again proper
and an isomorphism over `𝐀¹_X`, so Stacks 0F9J gives classes `C ∈ A⁰(W_∞ ⟶ X)` and
`C' ∈ A⁰(W'_∞ ⟶ X)`. Stacks 0FAQ asserts

  `g_{∞,*} ∘ C' = C`  in  `A⁰(W_∞ ⟶ X)`,

where `g_∞ : W'_∞ ⟶ W_∞` is the restriction of `g` and `g_{∞,*} ∘ -` is the proper pushforward of
bivariant classes of Stacks 0EPK.

The proof is the one of the source. Given `α ∈ A_k(T)` on a test scheme `T ⟶ X`, choose a lift
`β' ∈ A_{k+1}(W'_T)` of `α` over the affine chart. Its pushforward `β = g_{T,*}β'` is a lift of `α`
on `W_T`, because `g_T` is an isomorphism over the chart (Stacks 02RG in the case of two
isomorphism legs). So `C ∩ α = i_∞^*β`, and Stacks 02TA turns this into
`g_{∞,T,*}((i'_∞)^*β') = g_{∞,T,*}(C' ∩ α)`.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.infinityMap`: the morphism `g_∞ : W'_∞ ⟶ W_∞`.
* `Stacks.Chow.GysinAtInfinity.testMap`: the base change `g_T : W'_T ⟶ W_T`.

## Main results

* `Stacks.Chow.GysinAtInfinity.properPushforward_gysinAtInfinityClass`: **Stacks 0FAQ**,
  `g_{∞,*} ∘ C' = C`.

## References

* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

/-! ### The geometry of a proper modification -/

section Geometry

variable {X W W' S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : W' ⟶ W)

/-- The restriction `g_∞ : W'_∞ ⟶ W_∞` of `g` to the fibres at infinity of `b ∘ g` and of `b`. -/
def infinityMap : modificationFibreAtInfinity f (g ≫ b) ⟶ modificationFibreAtInfinity f b :=
  pullback.lift (pullback.fst (g ≫ b) (infinitySection f) ≫ g)
    (pullback.snd (g ≫ b) (infinitySection f)) (by rw [Category.assoc, pullback.condition])

/-- `g_∞` followed by the inclusion `W_∞ ⟶ W` is the inclusion `W'_∞ ⟶ W'` followed by `g`. -/
@[reassoc (attr := simp)]
theorem infinityMap_fst :
    infinityMap f b g ≫ modificationInclusionAtInfinity f b =
      modificationInclusionAtInfinity f (g ≫ b) ≫ g :=
  pullback.lift_fst _ _ _

/-- `g_∞` commutes with the projections of `W'_∞` and `W_∞` to the section at infinity. -/
@[reassoc (attr := simp)]
theorem infinityMap_snd :
    infinityMap f b g ≫ pullback.snd b (infinitySection f) =
      pullback.snd (g ≫ b) (infinitySection f) :=
  pullback.lift_snd _ _ _

/-- `g_∞` lies over `X`. -/
@[reassoc]
theorem infinityMap_comp_projection :
    infinityMap f b g ≫ modificationProjectionAtInfinity f b =
      modificationProjectionAtInfinity f (g ≫ b) := by
  simp only [modificationProjectionAtInfinity, modificationProjection, infinityMap_fst_assoc,
    Category.assoc]

/-- A map `p' ×_X T ⟶ p ×_X T` over `T` and over `g`, where `p' = g ≫ p`, exhibits the source as
the base change of the target along `g`. -/
private theorem isPullback_of_lift_comp {Y Y' Z Q : Scheme.{u}} (p : Y ⟶ Z) (p' : Y' ⟶ Z)
    (e : Y' ⟶ Y) (he : e ≫ p = p') (q : Q ⟶ Z) (m : pullback p' q ⟶ pullback p q)
    (h₁ : m ≫ pullback.fst p q = pullback.fst p' q ≫ e)
    (h₂ : m ≫ pullback.snd p q = pullback.snd p' q) :
    IsPullback m (pullback.fst p' q) (pullback.fst p q) e := by
  refine IsPullback.of_right ?_ h₁ (IsPullback.of_hasPullback p q).flip
  rw [h₂]
  subst he
  exact (IsPullback.of_hasPullback _ q).flip

/-- `W'_∞` is the base change of `W_∞` along `g`. -/
theorem isPullback_infinityMap :
    IsPullback (infinityMap f b g) (modificationInclusionAtInfinity f (g ≫ b))
      (modificationInclusionAtInfinity f b) g :=
  isPullback_of_lift_comp b (g ≫ b) g rfl _ _ (infinityMap_fst f b g) (infinityMap_snd f b g)

/-- If `g` is proper, then so is `g_∞ : W'_∞ ⟶ W_∞`. -/
instance isProper_infinityMap [IsProper g] : IsProper (infinityMap f b g) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_infinityMap f b g).flip inferInstance

/-- The open `(b ∘ g)⁻¹(𝐀¹_X) ⊆ W'` maps to `b⁻¹(𝐀¹_X) ⊆ W`. -/
def chartMap : chartOpen f (g ≫ b) ⟶ chartOpen f b :=
  pullback.lift (chartInclusion f (g ≫ b) ≫ g) (pullback.snd (g ≫ b) (projectiveLineAffineChart f))
    (by rw [Category.assoc, pullback.condition])

/-- The map of affine charts commutes with their inclusions into `W'` and `W` and with `g`. -/
@[reassoc (attr := simp)]
theorem chartMap_fst : chartMap f b g ≫ chartInclusion f b = chartInclusion f (g ≫ b) ≫ g :=
  pullback.lift_fst _ _ _

/-- The map of affine charts commutes with their projections to `𝐀¹_X`. -/
@[reassoc (attr := simp)]
theorem chartMap_snd :
    chartMap f b g ≫ pullback.snd b (projectiveLineAffineChart f) =
      pullback.snd (g ≫ b) (projectiveLineAffineChart f) :=
  pullback.lift_snd _ _ _

/-- `(b ∘ g)⁻¹(𝐀¹_X)` is the inverse image of `b⁻¹(𝐀¹_X)` under `g`. -/
theorem isPullback_chartMap :
    IsPullback (chartInclusion f (g ≫ b)) (chartMap f b g) g (chartInclusion f b) :=
  (isPullback_of_lift_comp b (g ≫ b) g rfl _ _ (chartMap_fst f b g) (chartMap_snd f b g)).flip

/-- If `g` is an isomorphism over `b⁻¹(𝐀¹_X)`, then `b ∘ g` is an isomorphism over `𝐀¹_X` as
soon as `b` is. -/
theorem isIso_pullbackSnd_comp [IsIso (pullback.snd b (projectiveLineAffineChart f))]
    [IsIso (pullback.snd g (chartInclusion f b))] :
    IsIso (pullback.snd (g ≫ b) (projectiveLineAffineChart f)) := by
  have h : pullback.snd (g ≫ b) (projectiveLineAffineChart f) =
      (pullbackRightPullbackFstIso b (projectiveLineAffineChart f) g).inv ≫
        pullback.snd g (chartInclusion f b) ≫ pullback.snd b (projectiveLineAffineChart f) := by
    rw [← pullbackRightPullbackFstIso_hom_snd, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- If `b` and `b ∘ g` are isomorphisms over `𝐀¹_X`, then the map of affine charts
`(b ∘ g)⁻¹(𝐀¹_X) ⟶ b⁻¹(𝐀¹_X)` is an isomorphism. -/
theorem isIso_chartMap [IsIso (pullback.snd b (projectiveLineAffineChart f))]
    [IsIso (pullback.snd (g ≫ b) (projectiveLineAffineChart f))] : IsIso (chartMap f b g) := by
  have : IsIso (chartMap f b g ≫ pullback.snd b (projectiveLineAffineChart f)) := by
    rw [chartMap_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd b (projectiveLineAffineChart f))

variable {T : Scheme.{u}} (t : T ⟶ X)

/-- The base change `g_T : W' ×_X T ⟶ W ×_X T` of `g`. -/
def testMap :
    pullback (modificationProjection f (g ≫ b)) t ⟶ pullback (modificationProjection f b) t :=
  pullback.lift (pullback.fst (modificationProjection f (g ≫ b)) t ≫ g)
    (pullback.snd (modificationProjection f (g ≫ b)) t)
    (by rw [Category.assoc, ← pullback.condition]; simp [modificationProjection])

/-- `g_T` commutes with the projections `W'_T ⟶ W'` and `W_T ⟶ W` and with `g`. -/
@[reassoc (attr := simp)]
theorem testMap_fst :
    testMap f b g t ≫ pullback.fst (modificationProjection f b) t =
      pullback.fst (modificationProjection f (g ≫ b)) t ≫ g :=
  pullback.lift_fst _ _ _

/-- `g_T` lies over `T`. -/
@[reassoc (attr := simp)]
theorem testMap_snd :
    testMap f b g t ≫ pullback.snd (modificationProjection f b) t =
      pullback.snd (modificationProjection f (g ≫ b)) t :=
  pullback.lift_snd _ _ _

/-- `W'_T` is the base change of `W_T` along `g`. -/
theorem isPullback_testMap :
    IsPullback (testMap f b g t) (pullback.fst (modificationProjection f (g ≫ b)) t)
      (pullback.fst (modificationProjection f b) t) g :=
  isPullback_of_lift_comp _ _ g (by simp [modificationProjection]) t _ (testMap_fst f b g t)
    (testMap_snd f b g t)

/-- If `g` is proper, then so is its base change `g_T : W'_T ⟶ W_T`. -/
instance isProper_testMap [IsProper g] : IsProper (testMap f b g t) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_testMap f b g t).flip inferInstance

/-- The base change of `g_∞ : W'_∞ ⟶ W_∞` to `T`. -/
def testInfinityMap :
    pullback (modificationProjectionAtInfinity f (g ≫ b)) t ⟶
      pullback (modificationProjectionAtInfinity f b) t :=
  pullback.lift (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫ infinityMap f b g)
    (pullback.snd (modificationProjectionAtInfinity f (g ≫ b)) t)
    (by rw [Category.assoc, infinityMap_comp_projection, pullback.condition])

/-- The base change of `g_∞` to `T` commutes with the projections to `W'_∞` and `W_∞` and with
`g_∞`. -/
@[reassoc (attr := simp)]
theorem testInfinityMap_fst :
    testInfinityMap f b g t ≫ pullback.fst (modificationProjectionAtInfinity f b) t =
      pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫ infinityMap f b g :=
  pullback.lift_fst _ _ _

/-- The base change of `g_∞` to `T` lies over `T`. -/
@[reassoc (attr := simp)]
theorem testInfinityMap_snd :
    testInfinityMap f b g t ≫ pullback.snd (modificationProjectionAtInfinity f b) t =
      pullback.snd (modificationProjectionAtInfinity f (g ≫ b)) t :=
  pullback.lift_snd _ _ _

/-- `W'_∞ ×_X T` is the base change of `W_∞ ×_X T` along `g_∞`. -/
theorem isPullback_testInfinityMap :
    IsPullback (testInfinityMap f b g t)
      (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t)
      (pullback.fst (modificationProjectionAtInfinity f b) t) (infinityMap f b g) :=
  isPullback_of_lift_comp _ _ _ (infinityMap_comp_projection f b g) t _
    (testInfinityMap_fst f b g t) (testInfinityMap_snd f b g t)

/-- If `g` is proper, then so is the base change of `g_∞` to `T`. -/
instance isProper_testInfinityMap [IsProper g] : IsProper (testInfinityMap f b g t) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_testInfinityMap f b g t).flip
    inferInstance

/-- The base changes of `g` and of `g_∞` commute with the inclusions of the fibres at infinity. -/
@[reassoc]
theorem testInfinityMap_comp_modificationInfinityBaseChange :
    testInfinityMap f b g t ≫ modificationInfinityBaseChange f b t =
      modificationInfinityBaseChange f (g ≫ b) t ≫ testMap f b g t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, modificationInfinityBaseChange_comp_fst, testMap_fst,
      ← Category.assoc (modificationInfinityBaseChange f (g ≫ b) t),
      modificationInfinityBaseChange_comp_fst, testInfinityMap_fst_assoc, infinityMap_fst,
      Category.assoc]
  · simp only [Category.assoc, modificationInfinityBaseChange_comp_snd, testMap_snd,
      testInfinityMap_snd]

/-- The base change `U' ×_X T ⟶ U ×_X T` of the map of affine charts. -/
def testChartMap :
    pullback (chartInclusion f (g ≫ b) ≫ modificationProjection f (g ≫ b)) t ⟶
      pullback (chartInclusion f b ≫ modificationProjection f b) t :=
  pullback.map _ t _ t (chartMap f b g) (𝟙 T) (𝟙 X)
    (by rw [Category.comp_id, chartMap_fst_assoc]; simp [modificationProjection]) (by simp)

/-- The base change of the map of affine charts commutes with the projections to the charts. -/
@[reassoc (attr := simp)]
theorem testChartMap_fst :
    testChartMap f b g t ≫ pullback.fst (chartInclusion f b ≫ modificationProjection f b) t =
      pullback.fst (chartInclusion f (g ≫ b) ≫ modificationProjection f (g ≫ b)) t ≫
        chartMap f b g :=
  pullback.lift_fst _ _ _

/-- The base change of the map of affine charts lies over `T`. -/
@[reassoc (attr := simp)]
theorem testChartMap_snd :
    testChartMap f b g t ≫ pullback.snd (chartInclusion f b ≫ modificationProjection f b) t =
      pullback.snd (chartInclusion f (g ≫ b) ≫ modificationProjection f (g ≫ b)) t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- If the map of affine charts is an isomorphism, then so is its base change to `T`. -/
instance isIso_testChartMap [IsIso (chartMap f b g)] : IsIso (testChartMap f b g t) := by
  unfold testChartMap
  infer_instance

/-- The open part `U' ×_X T` of `W'_T` is the inverse image of the open part `U ×_X T` of `W_T`. -/
theorem isPullback_testChartMap :
    IsPullback (openBaseChange (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b)) t)
      (testChartMap f b g t) (testMap f b g t)
      (openBaseChange (modificationProjection f b) (chartInclusion f b) t) := by
  refine IsPullback.of_bot ?_ ?_
    (isPullback_openBaseChange (modificationProjection f b) (chartInclusion f b) t).flip
  · rw [testChartMap_fst, testMap_fst]
    exact (isPullback_openBaseChange (modificationProjection f (g ≫ b))
      (chartInclusion f (g ≫ b)) t).flip.paste_vert (isPullback_chartMap f b g)
  · refine pullback.hom_ext ?_ ?_ <;> simp

end Geometry

/-! ### The class at infinity of a proper modification -/

section Transport

variable (C : ChowSituation.{u})

/-- A pushforward along the transport between two equal closed subschemes that carries `x` to `y`
exhibits `x` and `y` as heterogeneously equal. -/
theorem heq_of_chowPushforwardOfIso_eqToHom {Y : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    (k : ℤ) {D D' : Y.IdealSheafData} (hD : D = D')
    (hbase : eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ (D'.subschemeι ≫ p) =
      D.subschemeι ≫ p)
    {x : chowGroup C (D.subschemeι ≫ p) k} {y : chowGroup C (D'.subschemeι ≫ p) k}
    (h : chowPushforwardOfIso C (D.subschemeι ≫ p) (D'.subschemeι ≫ p)
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD)) hbase k x = y) : x ≍ y := by
  subst hD
  subst h
  exact heq_of_eq (chowPushforwardOfIso_id C _ k x).symm

/-- Conversely, heterogeneously equal classes on two equal closed subschemes correspond under the
pushforward along the transport. -/
theorem chowPushforwardOfIso_eqToHom_eq_of_heq {Y : Scheme.{u}} (p : Y ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {D D' : Y.IdealSheafData} (hD : D = D')
    (hbase : eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ (D'.subschemeι ≫ p) =
      D.subschemeι ≫ p)
    {x : chowGroup C (D.subschemeι ≫ p) k} {y : chowGroup C (D'.subschemeι ≫ p) k}
    (h : x ≍ y) :
    chowPushforwardOfIso C (D.subschemeι ≫ p) (D'.subschemeι ≫ p)
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD)) hbase k x = y := by
  subst hD
  cases h
  exact chowPushforwardOfIso_id C _ k x

variable {A P : Scheme.{u}} (p : A ⟶ C.S) [LocallyOfFiniteType p] (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (k : ℤ) (x : chowGroup C p (k + 1))

/-- The Gysin map at a section pulled back along a morphism only depends on the morphism. -/
theorem onChow_pullback_heq {d d' : A ⟶ P} (h : d = d') :
    (gysinSystemOfInvertible C).onChow p ((Scheme.Modules.pullback d).obj L)
        (AlgebraicGeometry.pullbackGlobalSections d L s) k x ≍
      (gysinSystemOfInvertible C).onChow p ((Scheme.Modules.pullback d').obj L)
        (AlgebraicGeometry.pullbackGlobalSections d' L s) k x := by
  subst h
  rfl

/-- The Gysin map at a section pulled back in two steps is that at the section pulled back along
the composite. -/
theorem onChow_pullbackComp_heq {B : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ P) :
    (gysinSystemOfInvertible C).onChow p
        ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) k x ≍
      (gysinSystemOfInvertible C).onChow p ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (q₁ ≫ q₂) L s) k x :=
  heq_of_chowPushforwardOfIso_eqToHom C p k (Stacks.Divisors.zeroScheme_pullback_comp q₁ q₂ L s) _
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C q₁ q₂ p L s k x)

/-- The Gysin map at a section pulled back in three steps is that at the section pulled back in two
steps along morphisms with the same composite. -/
theorem onChow_pullback₃_heq {B B' Q : Scheme.{u}} (a₁ : A ⟶ B) (a₂ : B ⟶ Q) (a₃ : Q ⟶ P)
    (c₁ : A ⟶ B') (c₂ : B' ⟶ P) (h : (a₁ ≫ a₂) ≫ a₃ = c₁ ≫ c₂) :
    (gysinSystemOfInvertible C).onChow p
        ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback a₂).obj
          ((Scheme.Modules.pullback a₃).obj L)))
        (AlgebraicGeometry.pullbackGlobalSections a₁
          ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback a₃).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a₂ ((Scheme.Modules.pullback a₃).obj L)
            (AlgebraicGeometry.pullbackGlobalSections a₃ L s))) k x ≍
      (gysinSystemOfInvertible C).onChow p
        ((Scheme.Modules.pullback c₁).obj ((Scheme.Modules.pullback c₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections c₁ ((Scheme.Modules.pullback c₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections c₂ L s)) k x :=
  (onChow_pullbackComp_heq C p _ _ k x a₁ a₂).trans
    ((onChow_pullbackComp_heq C p L s k x (a₁ ≫ a₂) a₃).trans
      ((onChow_pullback_heq C p L s k x h).trans (onChow_pullbackComp_heq C p L s k x c₁ c₂).symm))

omit [LocallyOfFiniteType p] in
/-- The zero schemes of a section pulled back in three steps and in two steps along morphisms with
the same composite agree. -/
theorem zeroScheme_pullback₃_eq {B B' Q : Scheme.{u}} (a₁ : A ⟶ B) (a₂ : B ⟶ Q) (a₃ : Q ⟶ P)
    (c₁ : A ⟶ B') (c₂ : B' ⟶ P) (h : (a₁ ≫ a₂) ≫ a₃ = c₁ ≫ c₂) :
    Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback c₁).obj ((Scheme.Modules.pullback c₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections c₁ ((Scheme.Modules.pullback c₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections c₂ L s)) =
      Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback a₂).obj
          ((Scheme.Modules.pullback a₃).obj L)))
        (AlgebraicGeometry.pullbackGlobalSections a₁
          ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback a₃).obj L))
          (AlgebraicGeometry.pullbackGlobalSections a₂ ((Scheme.Modules.pullback a₃).obj L)
            (AlgebraicGeometry.pullbackGlobalSections a₃ L s))) := by
  rw [Stacks.Divisors.zeroScheme_pullback_comp a₁ a₂, Stacks.Divisors.zeroScheme_pullback_comp
    (a₁ ≫ a₂) a₃, h, Stacks.Divisors.zeroScheme_pullback_comp c₁ c₂]

/-- Two composable proper pushforwards equal three composable ones when the composite morphisms
agree. -/
theorem properChowPushforward_comp_eq_comp₃ {B D E F : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S)
    [LocallyOfFiniteType sD] (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (sF : F ⟶ C.S)
    [LocallyOfFiniteType sF] (u : A ⟶ B) [IsProper u] (v : B ⟶ F) [IsProper v] (w₁ : A ⟶ D)
    [IsProper w₁] (w₂ : D ⟶ E) [IsProper w₂] (w₃ : E ⟶ F) [IsProper w₃]
    (h : u ≫ v = w₁ ≫ w₂ ≫ w₃) (hu : u ≫ sB = sA) (hv : v ≫ sF = sB) (hw₁ : w₁ ≫ sD = sA)
    (hw₂ : w₂ ≫ sE = sD) (hw₃ : w₃ ≫ sF = sE) (m : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu m)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sF v hv m)
    (hfacw₁ : ProperPushforwardFactorsThroughRationalEquivalence C sA sD w₁ hw₁ m)
    (hfacw₂ : ProperPushforwardFactorsThroughRationalEquivalence C sD sE w₂ hw₂ m)
    (hfacw₃ : ProperPushforwardFactorsThroughRationalEquivalence C sE sF w₃ hw₃ m)
    (y : chowGroup C sA m) :
    properChowPushforward C sB sF v hv m hfacv (properChowPushforward C sA sB u hu m hfacu y) =
      properChowPushforward C sE sF w₃ hw₃ m hfacw₃
        (properChowPushforward C sD sE w₂ hw₂ m hfacw₂
          (properChowPushforward C sA sD w₁ hw₁ m hfacw₁ y)) := by
  rw [properChowPushforward_comp_eq C sA sB sE sF u v (w₁ ≫ w₂) w₃ (by rw [h, Category.assoc])
    hu hv (by rw [Category.assoc, hw₂, hw₁]) hw₃ m hfacu hfacv
    (properPushforwardDescends C _ _ _ _ _) hfacw₃ y,
    properChowPushforward_comp_apply C sA sD sE w₁ w₂ (w₁ ≫ w₂) rfl hw₁ hw₂ _ m hfacw₁ hfacw₂]

/-- Proper pushforward commutes with the transport of Chow groups along an equality of
degrees. -/
theorem properChowPushforward_chowGroupDegreeEquiv_eq {B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ sB = sA) {m n : ℤ} (hmn : m = n)
    (hfacm : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu m)
    (hfacn : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu n)
    (y : chowGroup C sA m) :
    properChowPushforward C sA sB u hu n hfacn (chowGroupDegreeEquiv C sA hmn y) =
      chowGroupDegreeEquiv C sB hmn (properChowPushforward C sA sB u hu m hfacm y) := by
  subst hmn
  rfl

/-- The cap operation of the proper pushforward of Stacks 0EPK of a class read for a morphism equal
to the composite `f ≫ g`: it pushes the cap forward along any morphism `T ×_Z X ⟶ T ×_Z Y` lying
over `f` and over `T`. -/
theorem canonicalBivariantProperPushforward_copy_cap {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (q : X ⟶ Z) [LocallyOfFiniteType q] (hq : q = f ≫ g) (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (hqs : q ≫ sZ = sX) (p : ℤ) (c : CanonicalBivariantClass C sX sZ q hqs p) {T : Scheme.{u}}
    (t : T ⟶ Z) [LocallyOfFiniteType t] (m : pullback q t ⟶ pullback g t) [IsProper m]
    (hm₁ : m ≫ pullback.fst g t = pullback.fst q t ≫ f)
    (hm₂ : m ≫ pullback.snd g t = pullback.snd q t)
    (hms : m ≫ (pullback.fst g t ≫ sY) = pullback.fst q t ≫ sX) (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    (canonicalBivariantProperPushforward C sX sY sZ f g hf hg p
        (BivariantClass.copy C (canonicalGysinSystem C) sX sZ hq hqs
          (comp_comp_structureMorphism_eq hf hg) rfl c)).cap t k α =
      properChowPushforward C (pullback.fst q t ≫ sX) (pullback.fst g t ≫ sY) m hms (k - p)
        (properPushforwardDescends C _ _ _ _ _) (c.cap t k α) := by
  subst hq
  obtain rfl : m = bivariantPushforwardBaseChange f g t :=
    pullback.hom_ext (by rw [hm₁, bivariantPushforwardBaseChange_fst])
      (by rw [hm₂, bivariantPushforwardBaseChange_snd])
  rfl

end Transport

section Chow

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor isIso_pullbackSnd_comp

variable (C : ChowSituation.{u}) {X W W' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : W' ⟶ W) [IsProper g]
  {T : Scheme.{u}} (t : T ⟶ X)

omit [LocallyOfFiniteType f] [IsProper b] [IsProper g] in
/-- `g_T` commutes with the structure morphisms of `W'_T` and `W_T` to the base. -/
theorem testMap_comp_testStr :
    testMap f b g t ≫ testStr C f (modificationProjection f b) t =
      testStr C f (modificationProjection f (g ≫ b)) t := by
  simp [testStr, modificationProjection]

omit [LocallyOfFiniteType f] [IsProper b] [IsProper g] in
/-- The base change of the map of affine charts commutes with the structure morphisms of
`U' ×_X T` and `U ×_X T` to the base. -/
theorem testChartMap_comp_openStr :
    testChartMap f b g t ≫ openStr C f (modificationProjection f b) (chartInclusion f b) t =
      openStr C f (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b)) t := by
  simp [openStr]

omit [LocallyOfFiniteType f] [IsProper b] [IsProper g] in
/-- The base change of `g_∞` to `T` commutes with the structure morphisms of `W'_∞ ×_X T` and
`W_∞ ×_X T` to the base. -/
theorem testInfinityMap_comp_structure :
    testInfinityMap f b g t ≫ (pullback.fst (modificationProjectionAtInfinity f b) t ≫
        (modificationProjectionAtInfinity f b ≫ f)) =
      pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫
        (modificationProjectionAtInfinity f (g ≫ b) ≫ f) := by
  rw [testInfinityMap_fst_assoc, ← Category.assoc (infinityMap f b g),
    infinityMap_comp_projection]

variable [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  [IsIso (pullback.snd g (chartInclusion f b))] [LocallyOfFiniteType t]

/-- **Lifts and proper modifications.** If `β' ∈ A_{k+1}(W'_T)` restricts over the affine chart to
the flat pullback of `α`, so does its pushforward to `W_T`: over the chart `W'_T ⟶ W_T` is an
isomorphism, and flat pullback commutes with pushforward along it (Stacks 02RG). -/
theorem isLift_testMap {k : ℤ} {α : chowGroup C (t ≫ f) k}
    {β' : chowGroup C (testStr C f (modificationProjection f (g ≫ b)) t) (k + 1)}
    (hβ' : IsLift C f (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b))
      (relativeDimension_chartInclusion_comp f (g ≫ b)) t k α β') :
    IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) t k α
      (properChowPushforward C (testStr C f (modificationProjection f (g ≫ b)) t)
        (testStr C f (modificationProjection f b) t) (testMap f b g t)
        (testMap_comp_testStr C f b g t) (k + 1) (properPushforwardDescends C _ _ _ _ _) β') := by
  have := isOpenImmersion_openBaseChange (modificationProjection f b) (chartInclusion f b) t
  have := isOpenImmersion_openBaseChange (modificationProjection f (g ≫ b))
    (chartInclusion f (g ≫ b)) t
  have := isIso_chartMap f b g
  unfold IsLift at hβ' ⊢
  rw [chowGroupRestrict_properChowPushforward C
    (testStr C f (modificationProjection f (g ≫ b)) t)
    (testStr C f (modificationProjection f b) t)
    (openStr C f (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b)) t)
    (openStr C f (modificationProjection f b) (chartInclusion f b) t) (testMap f b g t)
    (testMap_comp_testStr C f b g t)
    (openBaseChange (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b)) t)
    (openBaseChange_comp_testStr C f _ _ t)
    (openBaseChange (modificationProjection f b) (chartInclusion f b) t)
    (openBaseChange_comp_testStr C f _ _ t) (testChartMap f b g t)
    (testChartMap_comp_openStr C f b g t) (isPullback_testChartMap f b g t) (k + 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β', hβ']
  have h := flatPullbackChow_chowPushforwardOfIso C (t ≫ f)
    (openStr C f (modificationProjection f (g ≫ b)) (chartInclusion f (g ≫ b)) t) (t ≫ f)
    (openStr C f (modificationProjection f b) (chartInclusion f b) t) (𝟙 T)
    (Category.id_comp _) (testChartMap f b g t) (testChartMap_comp_openStr C f b g t)
    (pullback.snd (chartInclusion f (g ≫ b) ≫ modificationProjection f (g ≫ b)) t) rfl
    (pullback.snd (chartInclusion f b ≫ modificationProjection f b) t) rfl
    (by rw [Category.comp_id, testChartMap_snd]) 1
    (relativeDimension_openSnd _ _ (relativeDimension_chartInclusion_comp f (g ≫ b)) t)
    (relativeDimension_openSnd _ _ (relativeDimension_chartInclusion_comp f b) t) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α
  rw [chowPushforwardOfIso_id] at h
  exact h.symm

omit [LocallyOfFiniteType f] [IsProper b] [IsProper g]
  [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  [IsIso (pullback.snd g (chartInclusion f b))] [LocallyOfFiniteType t] in
/-- On the divisors at infinity of `W'_T` and `W_T`, the base change of `g_∞` is the morphism of
zero schemes induced by `g_T`. -/
theorem testInfinityIso_comp_testInfinityMap
    (E : testInfinityDivisor C f (g ≫ b) t =
      pullbackZeroScheme (testMap f b g t)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) t))) :
    testInfinityIso C f (g ≫ b) t ≫ testInfinityMap f b g t =
      eqToHom (congrArg Scheme.IdealSheafData.subscheme E) ≫
        zeroSchemePullbackHom (testMap f b g t)
          (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
          (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
            (pullback.fst (modificationProjection f b) t)) ≫
        testInfinityIso C f b t := by
  rw [← cancel_mono (modificationInfinityBaseChange f b t), Category.assoc, Category.assoc,
    Category.assoc, testInfinityMap_comp_modificationInfinityBaseChange,
    testInfinityIso_comp_modificationInfinityBaseChange,
    ← Category.assoc (testInfinityIso C f (g ≫ b) t),
    testInfinityIso_comp_modificationInfinityBaseChange, zeroSchemePullbackHom_subschemeι,
    ← Category.assoc, Stacks.Chow.subschemeι_eqToHom E]

/-- **The cap of the class at infinity of a modification, pushed forward.** On a test scheme
`t : T ⟶ X`, pushing `C' ∩ α` forward along the base change of `g_∞` gives `C ∩ α`. -/
theorem testInfinityMap_cap (k : ℤ) (α : chowGroup C (t ≫ f) k) :
    properChowPushforward C
        (pullback.fst (modificationProjectionAtInfinity f (g ≫ b)) t ≫
          (modificationProjectionAtInfinity f (g ≫ b) ≫ f))
        (pullback.fst (modificationProjectionAtInfinity f b) t ≫
          (modificationProjectionAtInfinity f b ≫ f))
        (testInfinityMap f b g t) (testInfinityMap_comp_structure C f b g t) (k - 0)
        (properPushforwardDescends C _ _ _ _ _)
        ((gysinAtInfinityClass C f (g ≫ b) inferInstance).cap t k α) =
      (gysinAtInfinityClass C f b inferInstance).cap t k α := by
  obtain ⟨β', hβ'⟩ := exists_isLift C f (modificationProjection f (g ≫ b))
    (chartInclusion f (g ≫ b)) (relativeDimension_chartInclusion_comp f (g ≫ b)) t k α
  rw [gysinAtInfinityClass_cap_eq_of_isLift C f (g ≫ b) inferInstance t hβ',
    gysinAtInfinityClass_cap_eq_of_isLift C f b inferInstance t (isLift_testMap C f b g t hβ'),
    properChowPushforward_chowGroupDegreeEquiv_eq C _ _ _ _ (sub_zero k).symm
      (properPushforwardDescends C _ _ _ _ _)]
  refine congrArg (chowGroupDegreeEquiv C _ (sub_zero k).symm) ?_
  have E := zeroScheme_pullback₃_eq (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) (testMap f b g t)
    (pullback.fst (modificationProjection f b) t) (lineMap f b)
    (pullback.fst (modificationProjection f (g ≫ b)) t) (lineMap f (g ≫ b))
    (by simp [lineMap, modificationProjection])
  rw [gysinSystemOfInvertible_isNaturalUnderProperPushforward C
    (testStr C f (modificationProjection f (g ≫ b)) t) (testStr C f (modificationProjection f b) t)
    (testMap f b g t) (testMap_comp_testStr C f b g t)
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) t))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) t)) k
    (zeroSchemePullbackHom (testMap f b g t) _ _) (zeroSchemePullbackHom_subschemeι _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) β',
    ← chowPushforwardOfIso_eqToHom_eq_of_heq C (testStr C f (modificationProjection f (g ≫ b)) t)
      k E (by rw [← Category.assoc, Stacks.Chow.subschemeι_eqToHom E])
      (onChow_pullback₃_heq C (testStr C f (modificationProjection f (g ≫ b)) t)
        (Stacks.Divisors.divisorSheaf (lineInfinityDivisor C.S))
        (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor C.S)) k β'
        (testMap f b g t) (pullback.fst (modificationProjection f b) t) (lineMap f b)
        (pullback.fst (modificationProjection f (g ≫ b)) t) (lineMap f (g ≫ b))
        (by simp [lineMap, modificationProjection])).symm]
  exact properChowPushforward_comp_eq_comp₃ C _ _ _ _ _ _ _ _ _ _
    (testInfinityIso_comp_testInfinityMap C f b g t E) _ _ _ _ _ k _ _ _ _ _ _

end Chow

/-! ### Stacks 0FAQ -/

section Statement

variable (C : ChowSituation.{u}) {X W W' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : W' ⟶ W) [IsProper g]

/-- **Stacks 0FAQ.** Let `X` be locally of finite type over the base of chapter 42, let
`b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let `g : W' ⟶ W` be proper and an
isomorphism over `𝐀¹_X`, that is, over `b⁻¹(𝐀¹_X)`. Let `C' ∈ A⁰(W'_∞ ⟶ X)` and
`C ∈ A⁰(W_∞ ⟶ X)` be the classes of Stacks 0F9J for `b ∘ g` and for `b`. Then

  `g_{∞,*} ∘ C' = C`  in  `A⁰(W_∞ ⟶ X)`,

where `g_∞ : W'_∞ ⟶ W_∞` is the restriction of `g` and the left side is the proper pushforward of
Stacks 0EPK. The class `C'` is read for the morphism `g_∞ ≫ (W_∞ ⟶ X)`, which equals the structure
morphism `W'_∞ ⟶ X`, through `Stacks.Chow.BivariantClass.copy`. -/
@[stacks 0FAQ]
theorem properPushforward_gysinAtInfinityClass
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (hg : IsIso (pullback.snd g (chartInclusion f b))) :
    haveI := hA
    haveI := hg
    canonicalBivariantProperPushforward C (modificationProjectionAtInfinity f (g ≫ b) ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f (infinityMap f b g)
        (modificationProjectionAtInfinity f b)
        (by rw [← Category.assoc, infinityMap_comp_projection]) rfl 0
        (BivariantClass.copy C (canonicalGysinSystem C)
          (modificationProjectionAtInfinity f (g ≫ b) ≫ f) f
          (infinityMap_comp_projection f b g).symm rfl
          (by rw [infinityMap_comp_projection]) rfl
          (gysinAtInfinityClass C f (g ≫ b) (isIso_pullbackSnd_comp f b g))) =
      gysinAtInfinityClass C f b hA := by
  have := hA
  have := hg
  refine BivariantClass.ext _ _ _ _ _ _ _ fun t _ k α ↦ ?_
  exact (canonicalBivariantProperPushforward_copy_cap C _ _ _ (infinityMap f b g)
    (modificationProjectionAtInfinity f b) (modificationProjectionAtInfinity f (g ≫ b))
    (infinityMap_comp_projection f b g).symm _ rfl rfl 0
    (gysinAtInfinityClass C f (g ≫ b) (isIso_pullbackSnd_comp f b g)) t
    (testInfinityMap f b g t) (testInfinityMap_fst f b g t) (testInfinityMap_snd f b g t)
    (testInfinityMap_comp_structure C f b g t) k α).trans (testInfinityMap_cap C f b g t k α)

end Statement

end GysinAtInfinity

end Stacks.Chow

end
