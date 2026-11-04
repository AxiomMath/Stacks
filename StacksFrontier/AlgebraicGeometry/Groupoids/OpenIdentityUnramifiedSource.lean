module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.UnramifiedLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# A groupoid scheme whose identity is open has unramified source

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose source and target maps are locally of
finite type and whose identity `e : U ⟶ R` is an open immersion. Then `s` is unramified, and if
moreover `s` is flat and locally of finite presentation then `s` is étale.

The argument is the *invariance of the unramified locus*. By **Stacks 047W** at unramifiedness,
read in the groupoid situation at `U' = U` and `g = 𝟙`, the largest open of `U ×_{𝟙, U, t} R` on
which the composite `h = pr₁ ≫ s` is unramified is the inverse image along `pr₀` of an open
`W ⊆ U`; that is the sense in which the locus is invariant. The identity gives a section
`σ : U ⟶ U ×_{𝟙, U, t} R` of `pr₀`, which is an open immersion because `pr₁` is an isomorphism —
the fibre product is taken along `𝟙` — and `σ ≫ h = e ≫ s = 𝟙`. So the image of `σ` is an open
on which `h` is unramified, hence is contained in `pr₀ ⁻¹ W`; since `σ` is a section of `pr₀`
that forces `W = ⊤`, and therefore `h`, and with it `s`, is unramified everywhere.

No joint monicity of `(t, s)` is used: the argument needs nothing beyond the groupoid axioms.
The same conclusion is reached by a different route, exhibiting the relative diagonal of `s` as a
base change of the identity, in
`Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity` of
`StacksFrontier.AlgebraicGeometry.Groupoids.EtaleOfOpenIdentity`, the last step of the proof of
**Stacks 04S6**.

## Main results

* `Stacks.Groupoids.GroupoidScheme.unramified_source_of_isOpenImmersion_identity`: the source map
  is unramified.
* `Stacks.Groupoids.GroupoidScheme.etale_source_of_flat_of_isOpenImmersion_identity`: it is étale
  when it is in addition flat and locally of finite presentation.
* `Stacks.Groupoids.GroupoidScheme.isIso_inverse`: the inverse of a groupoid scheme is an
  involution, hence an isomorphism.
* `Stacks.Groupoids.GroupoidScheme.unramified_target_of_isOpenImmersion_identity` and
  `Stacks.Groupoids.GroupoidScheme.etale_target_of_flat_of_isOpenImmersion_identity`: the same two
  conclusions for the target map, which the inverse carries to the source.

## Implementation notes

The fibre product `U ×_{𝟙, U, t} R` rather than `R` itself is what **Stacks 047W** speaks about,
and it is kept throughout instead of being replaced by `R` along the isomorphism
`pr₁ : U ×_{𝟙, U, t} R ≅ R`: the inverse of that isomorphism is
`Stacks.Groupoids.GroupoidScheme.targetPullbackInv`, built as the lift of `t` and `𝟙`, and it is
used only twice — once to see that the section through the identity is an open immersion, and
once at the very end to pass from `h` to `s`.

The step from unramifiedness to étaleness is the implication `Ω = 0` of **Stacks 02GV** in its
Mathlib form: an unramified morphism has an open-immersion relative diagonal
(`AlgebraicGeometry.Unramified.isOpenImmersion_diagonal`), hence is formally unramified, and a
flat formally unramified morphism locally of finite presentation is étale
(`AlgebraicGeometry.Etale.of_formallyUnramified_of_flat`).

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The compatibility making the identity arrow a point of `U ×_{𝟙, U, t} R`. -/
theorem id_comp_id_eq_identity_comp_target :
    𝟙 G.objects.left ≫ 𝟙 G.objects.left = G.identity.left ≫ G.target.left := by
  rw [Category.comp_id, identity_left_comp_target_left G]

/-- The section `U ⟶ U ×_{𝟙, U, t} R` of the first projection whose arrow component is the
identity arrow. -/
def identitySection : G.objects.left ⟶ pullback (𝟙 G.objects.left) G.target.left :=
  pullback.lift (𝟙 _) G.identity.left (id_comp_id_eq_identity_comp_target G)

/-- The identity section is a section of the first projection `U ×_{𝟙, U, t} R ⟶ U`. -/
@[reassoc]
theorem identitySection_comp_fst :
    identitySection G ≫ pullback.fst (𝟙 G.objects.left) G.target.left = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second projection carries the identity section to the identity `e : U ⟶ R`. -/
@[reassoc]
theorem identitySection_comp_snd :
    identitySection G ≫ pullback.snd (𝟙 G.objects.left) G.target.left = G.identity.left :=
  pullback.lift_snd _ _ _

/-- The compatibility making an arrow a point of `U ×_{𝟙, U, t} R` through its target. -/
theorem target_comp_id_eq_id_comp_target :
    G.target.left ≫ 𝟙 G.objects.left = 𝟙 G.arrows.left ≫ G.target.left := by
  rw [Category.comp_id, Category.id_comp]

/-- The inverse of the second projection `U ×_{𝟙, U, t} R ⟶ R`, which is an isomorphism because
the fibre product is taken along the identity of `U`. -/
def targetPullbackInv : G.arrows.left ⟶ pullback (𝟙 G.objects.left) G.target.left :=
  pullback.lift G.target.left (𝟙 _) (target_comp_id_eq_id_comp_target G)

/-- The first projection carries `targetPullbackInv` to the target map `t : R ⟶ U`. -/
@[reassoc]
theorem targetPullbackInv_comp_fst :
    targetPullbackInv G ≫ pullback.fst (𝟙 G.objects.left) G.target.left = G.target.left :=
  pullback.lift_fst _ _ _

/-- `targetPullbackInv` is a right inverse of the second projection `U ×_{𝟙, U, t} R ⟶ R`. -/
@[reassoc]
theorem targetPullbackInv_comp_snd :
    targetPullbackInv G ≫ pullback.snd (𝟙 G.objects.left) G.target.left = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The second projection `U ×_{𝟙, U, t} R ⟶ R` is an isomorphism. -/
instance isIso_pullback_snd_id_target :
    IsIso (pullback.snd (𝟙 G.objects.left) G.target.left) := by
  refine ⟨targetPullbackInv G, ?_, targetPullbackInv_comp_snd G⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, targetPullbackInv_comp_fst, Category.id_comp, ← pullback.condition,
      Category.comp_id]
  · rw [Category.assoc, targetPullbackInv_comp_snd, Category.comp_id, Category.id_comp]

/-- If the identity `e : U ⟶ R` is an open immersion, so is the identity section
`U ⟶ U ×_{𝟙, U, t} R`. -/
instance isOpenImmersion_identitySection [IsOpenImmersion G.identity.left] :
    IsOpenImmersion (identitySection G) := by
  have h : identitySection G
      = G.identity.left ≫ inv (pullback.snd (𝟙 G.objects.left) G.target.left) := by
    rw [← identitySection_comp_snd G, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **The invariance step.** In the groupoid situation of **Stacks 047W**, a section of the first
projection along which the composite `h` is unramified forces `h` to be unramified everywhere.

The maximal unramified locus of `h` is the inverse image along the first projection of an open
`W` of `U'`; the image of the section is an open contained in it, and a section of the first
projection meets every fibre of the first projection over a point of `U'`, so `W = ⊤`. -/
theorem unramified_h_of_section_of_unramified
    (D : AlgebraicGeometry.LocallyOfFiniteTypeGroupoidSituation.{u})
    (σ : D.U' ⟶ D.fiberProduct) (hσoi : IsOpenImmersion σ)
    (hfst : σ ≫ pullback.fst D.g D.groupoid.target.left = 𝟙 D.U')
    (hσ : Unramified (σ ≫ D.h)) : Unramified D.h := by
  have := hσoi
  obtain ⟨W, hWmem, hWmax⟩ :=
    AlgebraicGeometry.exists_open_with_preimage_maximal_unramifiedLocus D
  -- the image of the section is an open on which `h` is unramified
  have hrange : Unramified ((Scheme.Hom.opensRange σ).ι ≫ D.h) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp σ, Category.assoc]
    exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ (unramified_of_etale _) hσ
  have hle := hWmax hrange
  -- a section of the first projection forces the open `W` to be everything
  have hsec : ∀ x : D.U', (pullback.fst D.g D.groupoid.target.left) (σ x) = x := fun x => by
    have h : (pullback.fst D.g D.groupoid.target.left) (σ x)
        = (σ ≫ pullback.fst D.g D.groupoid.target.left) x := rfl
    rw [hfst] at h
    exact h
  have htop : W = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx2 : (pullback.fst D.g D.groupoid.target.left) (σ x) ∈ W :=
      hle (⟨x, rfl⟩ : σ x ∈ Scheme.Hom.opensRange σ)
    rwa [hsec x] at hx2
  -- the maximal locus is therefore everything, the set of such opens being downward closed
  have hlet : (⊤ : (pullback D.g D.groupoid.target.left).Opens)
      ≤ pullback.fst D.g D.groupoid.target.left ⁻¹ᵁ W := fun y _ => by
    rw [htop]
    trivial
  -- the fibre product and `h` of the situation, spelled out
  have hmem : Unramified ((pullback.fst D.g D.groupoid.target.left ⁻¹ᵁ W).ι
      ≫ pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left) := hWmem
  have hup : Unramified ((⊤ : (pullback D.g D.groupoid.target.left).Opens).ι
      ≫ pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left) := by
    rw [← (pullback D.g D.groupoid.target.left).homOfLE_ι hlet, Category.assoc]
    exact MorphismProperty.comp_mem (@Unramified.{u}) _ _
      (unramified_of_etale ((pullback D.g D.groupoid.target.left).homOfLE hlet)) hmem
  show Unramified (pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left)
  have hdecomp : pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left
      = (pullback D.g D.groupoid.target.left).topIso.inv
        ≫ (⊤ : (pullback D.g D.groupoid.target.left).Opens).ι
          ≫ pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left := by
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  rw [hdecomp]
  exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ (unramified_of_etale _) hup

/-- **A groupoid scheme whose identity is an open immersion has unramified source.** Nothing is
assumed beyond the groupoid axioms, local finite type of the source and target maps, and that the
identity `e : U ⟶ R` is an open immersion; in particular the arrows of the groupoid are not
required to be determined by their source and target.

This is the invariance of the unramified locus of `s` under the groupoid: by **Stacks 047W** that
locus is the inverse image along `t` of an open of `U`, and the open immersion `e` exhibits a
section of `t` along which `s` restricts to the identity, so that open is all of `U`. -/
@[sga "3 VIB 2.7" "partial", sga "3 VIB 2.7.1" "special case"]
theorem unramified_source_of_isOpenImmersion_identity
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [IsOpenImmersion G.identity.left] : Unramified G.source.left := by
  have hh : Unramified
      (pullback.snd (𝟙 G.objects.left) G.target.left ≫ G.source.left) := by
    refine unramified_h_of_section_of_unramified
      { S := S, groupoid := G, U' := G.objects.left, g := 𝟙 G.objects.left }
      (identitySection G) (isOpenImmersion_identitySection G) (identitySection_comp_fst G) ?_
    have hid : identitySection G
        ≫ pullback.snd (𝟙 G.objects.left) G.target.left ≫ G.source.left
        = 𝟙 G.objects.left := by
      rw [← Category.assoc, identitySection_comp_snd, identity_left_comp_source_left G]
    show Unramified (identitySection G
      ≫ pullback.snd (𝟙 G.objects.left) G.target.left ≫ G.source.left)
    rw [hid]
    exact unramified_of_etale _
  have hdecomp : G.source.left
      = inv (pullback.snd (𝟙 G.objects.left) G.target.left)
        ≫ pullback.snd (𝟙 G.objects.left) G.target.left ≫ G.source.left := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hdecomp]
  exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ (unramified_of_etale _) hh

/-- Two composites of a groupoid scheme agree as soon as their two factors do: the compatibility
that a `CategoryTheory.Limits.pullback.lift` carries is a proposition, so it does not enter. -/
theorem comp_lift_congr {T : Over S} {x x' y y' : T ⟶ G.arrows}
    (hx : x = x') (hy : y = y')
    (w : x ≫ G.source = y ≫ G.target) (w' : x' ≫ G.source = y' ≫ G.target) :
    pullback.lift x y w ≫ G.comp = pullback.lift x' y' w' ≫ G.comp := by
  subst hx
  subst hy
  rfl

/-- **The inverse of a groupoid scheme is an involution**, hence an isomorphism. Nothing beyond
the groupoid axioms is used; in particular the arrows are not assumed determined by their source
and target, as they are in
`Stacks.Groupoids.GroupoidScheme.isIso_inverse_of_jointlyMono`.

On a generalized arrow `f` the computation is the usual one. Writing `g = f⁻¹`, the identity laws
give `(g⁻¹ ∘ g) ∘ f = id_{t(f)} ∘ f = f` and `g⁻¹ ∘ (g ∘ f) = g⁻¹ ∘ id_{s(f)} = g⁻¹`, and the two
left-hand sides agree by associativity, so `f = g⁻¹ = f⁻¹⁻¹`. -/
theorem isIso_inverse : IsIso G.inverse := by
  have hinv : G.inverse ≫ G.inverse = 𝟙 G.arrows := by
    refine overHom_ext _ _ fun T f => ?_
    rw [Category.comp_id]
    -- `b = f⁻¹` and `a = f⁻¹⁻¹`, with the two compatibilities their composites need
    have hb : (f ≫ G.inverse) ≫ G.source = f ≫ G.target := by
      rw [Category.assoc, G.source_inverse]
    have ha : ((f ≫ G.inverse) ≫ G.inverse) ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
      rw [Category.assoc, G.source_inverse]
    -- `a ∘ b = id_{t(b)}` and `b ∘ f = id_{s(f)}`
    have h1 : pullback.lift ((f ≫ G.inverse) ≫ G.inverse) (f ≫ G.inverse) ha ≫ G.comp
        = (f ≫ G.inverse) ≫ G.source ≫ G.identity :=
      G.left_inverse T (f ≫ G.inverse) ha
    have h2 : pullback.lift (f ≫ G.inverse) f hb ≫ G.comp = f ≫ G.source ≫ G.identity :=
      G.left_inverse T f hb
    -- the two witnesses associativity asks for
    have w1 : (pullback.lift ((f ≫ G.inverse) ≫ G.inverse) (f ≫ G.inverse) ha ≫ G.comp)
        ≫ G.source = f ≫ G.target := by
      rw [h1]
      simp only [Category.assoc, G.source_identity, Category.comp_id, G.source_inverse]
    have w2 : ((f ≫ G.inverse) ≫ G.inverse) ≫ G.source
        = (pullback.lift (f ≫ G.inverse) f hb ≫ G.comp) ≫ G.target := by
      rw [h2]
      simp only [Category.assoc, G.target_identity, Category.comp_id, G.source_inverse,
        G.target_inverse]
    have hassoc := G.assoc T ((f ≫ G.inverse) ≫ G.inverse) (f ≫ G.inverse) f ha hb w1 w2
    -- the left-hand side is `id_{t(f)} ∘ f = f`
    have e1 : (f ≫ G.inverse) ≫ G.source ≫ G.identity = f ≫ G.target ≫ G.identity := by
      rw [← Category.assoc (f ≫ G.inverse) G.source G.identity, hb, Category.assoc]
    have wli : (f ≫ G.target ≫ G.identity) ≫ G.source = f ≫ G.target := by
      simp only [Category.assoc, G.source_identity, Category.comp_id]
    have hLHS := (G.comp_lift_congr (h1.trans e1) (rfl : f = f) w1 wli).trans
      (G.left_identity T f wli)
    -- the right-hand side is `a ∘ id_{s(a)} = a`
    have hainv : ((f ≫ G.inverse) ≫ G.inverse) ≫ G.source = f ≫ G.source := by
      rw [ha, Category.assoc, G.target_inverse]
    have e2 : pullback.lift (f ≫ G.inverse) f hb ≫ G.comp
        = ((f ≫ G.inverse) ≫ G.inverse) ≫ G.source ≫ G.identity := by
      rw [h2, ← Category.assoc ((f ≫ G.inverse) ≫ G.inverse) G.source G.identity, hainv,
        Category.assoc]
    have wri : ((f ≫ G.inverse) ≫ G.inverse) ≫ G.source
        = (((f ≫ G.inverse) ≫ G.inverse) ≫ G.source ≫ G.identity) ≫ G.target := by
      simp only [Category.assoc, G.target_identity, Category.comp_id]
    have hRHS := (G.comp_lift_congr (rfl : ((f ≫ G.inverse) ≫ G.inverse) = _) e2 w2 wri).trans
      (G.right_identity T ((f ≫ G.inverse) ≫ G.inverse) wri)
    rw [← Category.assoc]
    exact (hLHS.symm.trans (hassoc.trans hRHS)).symm
  exact ⟨⟨G.inverse, hinv, hinv⟩⟩

/-- **A groupoid scheme whose identity is an open immersion has unramified target.** The inverse
carries the target to the source and is an isomorphism, by
`Stacks.Groupoids.GroupoidScheme.isIso_inverse`. -/
@[sga "3 VIB 2.7" "partial"]
theorem unramified_target_of_isOpenImmersion_identity
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left]
    [IsOpenImmersion G.identity.left] : Unramified G.target.left := by
  have hs := unramified_source_of_isOpenImmersion_identity G
  have := G.isIso_inverse
  have : IsIso G.inverse.left := (Over.forget S).map_isIso G.inverse
  have h : G.target.left = G.inverse.left ≫ G.source.left :=
    congrArg Over.Hom.left G.source_inverse.symm
  rw [h]
  exact MorphismProperty.comp_mem (@Unramified.{u}) _ _ (unramified_of_etale _) hs

/-- **A groupoid scheme whose identity is an open immersion and whose source is flat and locally
of finite presentation has étale source.**

Unramifiedness is
`Stacks.Groupoids.GroupoidScheme.unramified_source_of_isOpenImmersion_identity`; an unramified
morphism has an open-immersion relative diagonal and is therefore formally unramified, and a flat
formally unramified morphism is étale. -/
@[sga "3 VIB 2.7" "(ii) ⇒ (i), (ii) ⇒ (iv)"]
theorem etale_source_of_flat_of_isOpenImmersion_identity
    [LocallyOfFiniteType G.target.left] [IsOpenImmersion G.identity.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Etale G.source.left := by
  have : LocallyOfFiniteType G.source.left := inferInstance
  have := unramified_source_of_isOpenImmersion_identity G
  exact Etale.of_formallyUnramified_of_flat _

/-- **A groupoid scheme whose identity is an open immersion and whose source is flat and locally
of finite presentation has étale target.** The inverse carries the target to the source and is an
isomorphism. -/
@[sga "3 VIB 2.7" "(ii) ⇒ (i), (ii) ⇒ (iv)"]
theorem etale_target_of_flat_of_isOpenImmersion_identity
    [LocallyOfFiniteType G.target.left] [IsOpenImmersion G.identity.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Etale G.target.left := by
  have := etale_source_of_flat_of_isOpenImmersion_identity G
  have := G.isIso_inverse
  have : IsIso G.inverse.left := (Over.forget S).map_isIso G.inverse
  have h : G.target.left = G.inverse.left ≫ G.source.left :=
    congrArg Over.Hom.left G.source_inverse.symm
  rw [h]
  infer_instance

end Stacks.Groupoids.GroupoidScheme

end
