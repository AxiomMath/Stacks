module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CategoryOfPrincipalHomogeneousSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsForChangeGroup

/-!
# The category of principal homogeneous spaces is fibred in groupoids

Let `B` be an algebraic space over a scheme `S`, let `G` be a group algebraic space over `B` and
let `p : G-Principal ⥤ (Sch/S)_fppf` be the functor of Stacks 04UN. Then `p` is fibred in
groupoids: a morphism `f : V ⟶ U` of the big fppf site of `S` lifts to the restriction
`(V, b ∘ f, X ×_U V)` of an object `(U, b, X)`, and fill-ins exist and are unique.

## Main results

* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.existsUnique_hom_of_base`: existence and
  uniqueness of fill-ins for `p`.
* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.projection_isFiberedInGroupoids`: `p` is
  fibred in groupoids.

## Implementation notes

Neither result carries a tag. Stacks 04UN asserts that the *fibre categories* of `p` are
groupoids, which is
`AlgebraicGeometry.Space.TorsorsFor.isIso_of_isIso_base`, and says nothing about
`p` being fibred over the site; Stacks 04UP asserts all three conditions of Stacks 02ZI for `p`
and asserts them only conjecturally, so it is not discharged by the first one.

The restriction of `(U, b, X)` along `f : V ⟶ U` is the fibre product `X ×_U V` with the action of
`V ×_{b ∘ f, B} G` obtained by carrying the action of `U ×_{b, B} G` through the
finite-product-preserving pullback functor (`AlgebraicGeometry.Space.restrictModObj`) and
transporting it along the comparison isomorphism `AlgebraicGeometry.Space.groupCompIso` of the two
descriptions of the acting group. That it is again a principal homogeneous space is the
pseudo-torsor condition under base change (`AlgebraicGeometry.Space.isPseudoTorsor_restrict`,
Stacks 04TW) together with the trivializing fpqc covering under base change
(`AlgebraicGeometry.Space.isFpqcCovering_pullback`, Stacks 03MR part (3)), the local sections
being carried along by the universal property of the fibre product.

## References

* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04TW](https://stacks.math.columbia.edu/tag/04TW)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u v

namespace AlgebraicGeometry.Space

open TorsorsFor hiding projection

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Base change of a principal homogeneous space -/

variable (𝒞 S hS) in
/-- The restriction of a principal homogeneous space along a morphism of algebraic spaces is a
principal homogeneous space. The pseudo-torsor condition of Stacks 04TW base changes by
`AlgebraicGeometry.Space.isPseudoTorsor_restrict`; the trivializing fpqc covering base changes by
`AlgebraicGeometry.Space.isFpqcCovering_pullback`, Stacks 03MR part (3); and a section of `X` over
a member `Bᵢ` of the old trivializing family gives one of `X ×_B B'` over `Bᵢ ×_B B'` by the
universal property of the fibre product. -/
private theorem isPrincipal_pullback (hB : IsAlgebraicSpace 𝒞 S hS B)
    (hB' : IsAlgebraicSpace 𝒞 S hS B') (b : B' ⟶ B) (G X : Over B) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace 𝒞 S hS G.left) (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    (h : IsPrincipalHomogeneousSpace 𝒞 S hS B hB G X hG hX) :
    IsPrincipalHomogeneousSpace 𝒞 S hS B' hB' ((Over.pullback b).obj G)
      ((Over.pullback b).obj X)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom b hG hB' hB)
      (isAlgebraicSpace_pullback 𝒞 S hS X.hom b hX hB' hB) := by
  obtain ⟨hp, I, Bᵢ, f, hBᵢ, hcov, hsec⟩ := h
  refine ⟨isPseudoTorsor_restrict b G X hp, I, fun i => pullback (f i) b,
    fun i => pullback.snd (f i) b,
    fun i => isAlgebraicSpace_pullback 𝒞 S hS (f i) b (hBᵢ i) hB' hB, ?_, fun i => ?_⟩
  · exact isFpqcCovering_pullback 𝒞 S hS (Y := (⟨B, hB⟩ : AlgebraicSpaces 𝒞 S hS))
      (X := (⟨B', hB'⟩ : AlgebraicSpaces 𝒞 S hS))
      (Yi := fun i => (⟨Bᵢ i, hBᵢ i⟩ : AlgebraicSpaces 𝒞 S hS))
      (fun i => ObjectProperty.homMk (f i)) (ObjectProperty.homMk b) hcov
  · obtain ⟨t, ht⟩ := (nonempty_unitHom_pullback_iff (f i) X).1 (hsec i)
    refine (nonempty_unitHom_pullback_iff (pullback.snd (f i) b)
      ((Over.pullback b).obj X)).2
      ⟨pullback.lift (pullback.fst (f i) b ≫ t) (pullback.snd (f i) b) ?_, ?_⟩
    · rw [Category.assoc, ht]
      exact pullback.condition
    · exact pullback.lift_snd _ _ _

variable {hB : IsAlgebraicSpace 𝒞 S hS B} {G : GroupAlgebraicSpace 𝒞 S hS B hB}

namespace PrincipalHomogeneousSpaces

/-! ### Restriction along a morphism of the site -/

/-- The action morphism of an object of `G-Principal` lies over the base. -/
private theorem actionMap_comp_hom (T : PrincipalHomogeneousSpaces hB G) :
    TorsorsFor.actionMap T ≫ T.total.hom =
      pullback.snd (pullback.snd G.obj.X.hom T.sec) T.total.hom ≫ T.total.hom :=
  (Over.w (γ[T.group, T.total])).trans pullback.condition

/-- The comparison of the group of the composite morphism to `B` with the pulled-back group, on
underlying objects. -/
private abbrev pullbackGroupIso (T : PrincipalHomogeneousSpaces hB G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    (fppfPullbackGroup hB G V (yoneda.map f ≫ T.sec)).obj.X ≅
      ((Over.pullback (yoneda.map f)).mapGrp.obj
        (fppfPullbackGroup hB G T.base T.sec).obj).X :=
  (Grp.forget (Over (yoneda.obj V))).mapIso (groupCompIso hB G T.sec (yoneda.map f))

private theorem isMonHom_pullbackGroupIso_symm (T : PrincipalHomogeneousSpaces hB G)
    {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) : IsMonHom (pullbackGroupIso T f).symm.hom :=
  (groupCompIso hB G T.sec (yoneda.map f)).inv.hom.isMonHom_hom

/-- The restriction of the action on an object of `G-Principal` along a morphism of bases. -/
private abbrev restrictAction (T : PrincipalHomogeneousSpaces hB G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    ModObj ((Over.pullback (yoneda.map f)).mapGrp.obj
      (fppfPullbackGroup hB G T.base T.sec).obj).X
      ((Over.pullback (yoneda.map f)).obj T.total) :=
  restrictModObj (yoneda.map f) T.group T.total

/-- The action on an object of `G-Principal` pulls back along a morphism of bases, after
identifying the pulled-back group with the group of the composite morphism to `B`. -/
@[instance_reducible]
private def pullbackAction (T : PrincipalHomogeneousSpaces hB G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) :
    ModObj (fppfPullbackGroup hB G V (yoneda.map f ≫ T.sec)).obj.X
      ((Over.pullback (yoneda.map f)).obj T.total) :=
  letI := restrictAction T f
  haveI := isMonHom_pullbackGroupIso_symm T f
  ModObj.ofIso (pullbackGroupIso T f).symm (Iso.refl _)

/-- The pulled-back action on the restriction of a principal homogeneous space along a morphism
of bases has invertible shear map. -/
private theorem pullbackAction_isPseudoTorsor (T : PrincipalHomogeneousSpaces hB G)
    {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) :
    letI := pullbackAction T f
    AlgebraicGeometry.IsPseudoTorsor
      (fppfPullbackGroup hB G V (yoneda.map f ≫ T.sec)).obj.X
      ((Over.pullback (yoneda.map f)).obj T.total) := by
  let := restrictAction T f
  have := isMonHom_pullbackGroupIso_symm T f
  exact isPseudoTorsor_ofIso_symm (pullbackGroupIso T f)
    (isPseudoTorsor_restrict (yoneda.map f) T.group T.total T.isPseudoTorsor)

/-- The restriction `(V, b ∘ f, X ×_U V)` of an object of `G-Principal` along a morphism
`f : V ⟶ U` of the big fppf site of `S`. -/
@[implicit_reducible]
private def pullbackPrincipal (T : PrincipalHomogeneousSpaces hB G) {V : BigFppfOver 𝒞 S hS}
    (f : V ⟶ T.base) : PrincipalHomogeneousSpaces hB G where
  base := V
  sec := yoneda.map f ≫ T.sec
  total := (Over.pullback (yoneda.map f)).obj T.total
  isAlgebraicSpace :=
    isAlgebraicSpace_pullback 𝒞 S hS T.total.hom (yoneda.map f) T.isAlgebraicSpace
      (isAlgebraicSpace_yoneda 𝒞 S hS V) (isAlgebraicSpace_yoneda 𝒞 S hS T.base)
  action := pullbackAction T f
  isTorsor := ⟨pullbackAction_isPseudoTorsor T f,
    (isPrincipal_pullback 𝒞 S hS
      (isAlgebraicSpace_yoneda 𝒞 S hS T.base) (isAlgebraicSpace_yoneda 𝒞 S hS V)
      (yoneda.map f) T.group T.total (fppfPullbackGroup hB G T.base T.sec).property
      T.isAlgebraicSpace T.isPrincipal).2⟩

/-- Composing the comparison map of the groups with the projection to the group of the base gives
the base change map of the groups along `f`. -/
private theorem pullbackPrincipal_groupComparison (T : PrincipalHomogeneousSpaces hB G)
    {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) :
    groupCompMap hB G T.sec (yoneda.map f) ≫
        pullback.fst (pullback.snd G.obj.X.hom T.sec) (yoneda.map f) =
      groupBaseChange (T := pullbackPrincipal T f) (T' := T) f rfl := by
  apply pullback.hom_ext
  · rw [Category.assoc, groupBaseChange_fst]
    exact groupCompMap_fst_fst T.sec (yoneda.map f)
  · rw [Category.assoc, pullback.condition, ← Category.assoc, groupCompMap_snd,
      groupBaseChange_snd]
    rfl

/-- The projection `X ×_U V ⟶ X` is a morphism of `G-Principal` from the restriction of
`(U, b, X)` along `f : V ⟶ U` to `(U, b, X)`, lying over `f`. -/
private def pullbackPrincipalHom (T : PrincipalHomogeneousSpaces hB G)
    {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) : pullbackPrincipal T f ⟶ T := by
  let F := Over.pullback (yoneda.map f)
  let e : (pullbackPrincipal T f).group ⟶ F.obj T.group :=
    (groupCompIso hB G T.sec (yoneda.map f)).hom.hom.hom
  let comparison := Functor.LaxMonoidal.μ F T.group T.total
  have ha : TorsorsFor.actionMap (pullbackPrincipal T f) =
      (e ▷ F.obj T.total).left ≫ comparison.left ≫ (F.map (γ[T.group, T.total])).left := by
    change (((e ⊗ₘ 𝟙 (F.obj T.total)) ≫
      (comparison ≫ F.map (γ[T.group, T.total]))) ≫ 𝟙 (F.obj T.total)).left = _
    simp only [Category.comp_id, MonoidalCategory.tensorHom_id, Over.comp_left]
  refine ⟨f, rfl, pullback.fst T.total.hom (yoneda.map f), IsPullback.of_hasPullback _ _, ?_⟩
  change TorsorsFor.actionMap (pullbackPrincipal T f) ≫ _ = _
  have hm : (e ▷ F.obj T.total).left ≫ comparison.left ≫
        pullback.fst (T.group ⊗ T.total).hom (yoneda.map f) =
      actionBaseChange (T := pullbackPrincipal T f) (T' := T) f rfl
        (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm := by
    apply pullback.hom_ext
    · simp only [comparison, F, Category.assoc, Over.μ_pullback_left_fst_fst,
        Over.whiskerRight_left_fst_assoc]
      exact (congrArg
        (pullback.fst (pullbackPrincipal T f).group.hom (F.obj T.total).hom ≫ ·)
        (pullbackPrincipal_groupComparison T f)).trans
          (actionBaseChange_fst (T := pullbackPrincipal T f) (T' := T) f rfl
            (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm).symm
    · simp only [comparison, F, Category.assoc, Over.μ_pullback_left_fst_snd,
        Over.whiskerRight_left_snd_assoc]
      exact (actionBaseChange_snd (T := pullbackPrincipal T f) (T' := T) f rfl
        (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm).symm
  rw [ha]
  change ((e ▷ F.obj T.total).left ≫ comparison.left ≫
    (F.map (γ[T.group, T.total])).left) ≫ _ = _
  simp only [F, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  change (e ▷ F.obj T.total).left ≫ comparison.left ≫
      pullback.fst (T.group ⊗ T.total).hom (yoneda.map f) ≫ TorsorsFor.actionMap T =
    actionBaseChange (T := pullbackPrincipal T f) (T' := T) f rfl
      (pullback.fst T.total.hom (yoneda.map f)) pullback.condition.symm ≫
        TorsorsFor.actionMap T
  refine Eq.trans (Eq.symm ((Category.assoc _ _ _).trans
    (congrArg (fun k => (e ▷ F.obj T.total).left ≫ k) (Category.assoc _ _ _))))
    (congrArg (fun k => k ≫ TorsorsFor.actionMap T) hm)

/-- The projection `X ×_U V ⟶ X` lies over `f : V ⟶ U`. -/
private theorem pullbackPrincipalHom_base (T : PrincipalHomogeneousSpaces hB G)
    {V : BigFppfOver 𝒞 S hS} (f : V ⟶ T.base) :
    Hom.base (pullbackPrincipalHom T f) = f :=
  rfl

/-! ### Fill-ins, and that `p` is fibred in groupoids -/

/-- Existence and uniqueness of fill-ins for `p : G-Principal ⥤ (Sch/S)_fppf`: given
`φ : T' ⟶ T`, `ψ : T'' ⟶ T` and a factorisation `f ∘ φ = ψ` of their base morphisms, there is a
unique morphism `T'' ⟶ T'` over `f` composing with `φ` to `ψ`. -/
theorem existsUnique_hom_of_base {T T' T'' : PrincipalHomogeneousSpaces hB G} (φ : T' ⟶ T)
    (ψ : T'' ⟶ T) (f : T''.base ⟶ T'.base) (hf : f ≫ Hom.base φ = Hom.base ψ) :
    ∃! χ : T'' ⟶ T', Hom.base χ = f ∧ χ ≫ φ = ψ := by
  have hb : yoneda.map f ≫ T'.sec = T''.sec := by
    rw [← Hom.comp_sec φ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hf,
      Hom.comp_sec ψ]
  have hw : Hom.map ψ ≫ T.total.hom =
      (T''.total.hom ≫ yoneda.map f) ≫ yoneda.map (Hom.base φ) := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hf]
    exact (Hom.isPullback ψ).w
  let g := (Hom.isPullback φ).lift (Hom.map ψ) (T''.total.hom ≫ yoneda.map f) hw
  have hg : g ≫ Hom.map φ = Hom.map ψ := (Hom.isPullback φ).lift_fst _ _ _
  have hg' : g ≫ T'.total.hom = T''.total.hom ≫ yoneda.map f :=
    (Hom.isPullback φ).lift_snd _ _ _
  have hp : IsPullback g T''.total.hom T'.total.hom (yoneda.map f) := by
    apply IsPullback.of_right (h₁₂ := Hom.map φ) (h₂₂ := yoneda.map (Hom.base φ)) _ hg'
      (Hom.isPullback φ)
    simpa only [hg, ← CategoryTheory.Functor.map_comp, hf] using (Hom.isPullback ψ)
  have he : TorsorsFor.actionMap T'' ≫ g =
      actionBaseChange f hb g hg'.symm ≫ TorsorsFor.actionMap T' := by
    apply (Hom.isPullback φ).hom_ext
    · calc
        _ = TorsorsFor.actionMap T'' ≫ Hom.map ψ := by rw [Category.assoc, hg]
        _ = actionBaseChange (Hom.base ψ) (Hom.comp_sec ψ) (Hom.map ψ)
            (Hom.isPullback ψ).w.symm ≫ TorsorsFor.actionMap T := Hom.smul_comp ψ
        _ = (actionBaseChange f hb g hg'.symm ≫
              actionBaseChange (Hom.base φ) (Hom.comp_sec φ) (Hom.map φ)
                (Hom.isPullback φ).w.symm) ≫ TorsorsFor.actionMap T := by
          simp only [actionBaseChange_comp, hf, hg]
        _ = actionBaseChange f hb g hg'.symm ≫
            actionBaseChange (Hom.base φ) (Hom.comp_sec φ) (Hom.map φ)
              (Hom.isPullback φ).w.symm ≫ TorsorsFor.actionMap T := Category.assoc _ _ _
        _ = actionBaseChange f hb g hg'.symm ≫ TorsorsFor.actionMap T' ≫ Hom.map φ :=
          congrArg (fun k => actionBaseChange f hb g hg'.symm ≫ k) (Hom.smul_comp φ).symm
        _ = _ := (Category.assoc _ _ _).symm
    · calc
        _ = TorsorsFor.actionMap T'' ≫ T''.total.hom ≫ yoneda.map f := by
          rw [Category.assoc, hg']
        _ = pullback.snd (pullback.snd G.obj.X.hom T''.sec) T''.total.hom ≫
            T''.total.hom ≫ yoneda.map f := by
          rw [← Category.assoc, actionMap_comp_hom, Category.assoc]
        _ = _ := by
          simp only [Category.assoc, actionMap_comp_hom, actionBaseChange_snd_assoc, hg']
  refine ⟨⟨f, hb, g, hp, he⟩, ⟨rfl, Hom.ext hf hg⟩, fun χ' hχ' => Hom.ext hχ'.1 ?_⟩
  exact (Hom.isPullback φ).hom_ext ((congrArg Hom.map hχ'.2).trans hg.symm)
    ((Hom.isPullback χ').w.trans (by rw [hχ'.1, ← hg']))

variable (hB G)

/-- The functor `p : G-Principal ⥤ (Sch/S)_fppf` of Stacks 04UN is fibred in groupoids. Every
morphism `f : V ⟶ U` of the big fppf site of `S` lifts to the restriction `(V, b ∘ f, X ×_U V)` of
an object `(U, b, X)` of `G-Principal` along `f`, which is again a principal homogeneous space
because the pseudo-torsor condition and the trivializing fpqc covering both base change, and
fill-ins exist and are unique by
`AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.existsUnique_hom_of_base`.

This is the first of the three conditions of Stacks 02ZI; it is not the conjecture of
Stacks 04UP, which asserts all three. -/
theorem projection_isFiberedInGroupoids : (projection hB G).IsFiberedInGroupoids where
  exists_lift := by
    intro V U f T hT
    subst hT
    refine ⟨pullbackPrincipal T f, pullbackPrincipalHom T f, ?_⟩
    rw [← pullbackPrincipalHom_base T f]
    exact show (projection hB G).IsHomLift
      ((projection hB G).map (pullbackPrincipalHom T f)) (pullbackPrincipalHom T f) from
      inferInstance
  unique_lift := existsUnique_hom_of_base

end PrincipalHomogeneousSpaces

end AlgebraicGeometry.Space

end
