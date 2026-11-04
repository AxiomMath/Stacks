module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset

/-!
# The existence half of Stacks 0GI3 is étale local

Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be closed with open
complement `U`, let `f : X' ⟶ X` be a morphism whose base change `f⁻¹(U) ⟶ U` is an
isomorphism, and let `W` be an algebraic space. Fix a morphism `w' : X' ⟶ W` and a morphism
`ŵ : X_{/T} ⟶ W` which are compatible on `X'_{/T}`. A *solution* over a morphism
`q : V ⟶ X` is a morphism `w_V : V ⟶ W` restricting to the base change of `w'` on
`X' ×_X V` and to the base change of `ŵ` on `V_{/q⁻¹T}`; a solution over `𝟙 X` is a morphism
`w : X ⟶ W` whose image under the comparison map of Stacks 0GI3 is `(w', ŵ)`. This file shows
that a solution over `X` exists as soon as solutions exist étale locally over the points of `T`
of an atlas: solutions are unique (Stacks 0GI1), restrict along morphisms, exist over every
étale chart contained in `U`, and glue.

## Main results

* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_etale_local`: the
  statement above.

## Implementation notes

Over a site object `V` étale over `X` two solutions agree by the uniqueness statement of Stacks
0GI1, which is the private lemma
`AlgebraicGeometry.Space.eq_of_eq_on_compl_of_eq_on_completion` of the file containing the
injectivity half of Stacks 0GI3: on `V ∖ q⁻¹T` both solutions are the composite of the inverse of
`f⁻¹(U) ⟶ U` with `w'`, and on `V_{/q⁻¹T}` both are the base change of `ŵ`. Over `U` the same
composite is a solution, the compatibility of `(w', ŵ)` providing the condition on completions.
The local solutions over the members of an étale covering of an atlas `V` glue, because `W` is a
sheaf and they agree on the fibre products of the members, to a morphism `V ⟶ W` which is again
a solution (being a solution is checked on a covering sieve), and that morphism descends to `X`
along the atlas (`AlgebraicGeometry.Space.existsUnique_hom_of_atlas_invariant`), the two
restrictions to the kernel pair being solutions over the same morphism. Finally a solution over
the atlas is a solution over `X`: the comparison with `w'` is checked on an atlas of the base
change `X' ×_X V`, and the comparison with `ŵ` on sections, after the surjective étale base
change of the atlas.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Restricting a solution -/

/-- If `v` satisfies the condition on `X' ×_X G` of a solution over `q`, then `z ≫ v = k ≫ w'`
for every `z : H ⟶ G` and `k : H ⟶ X'` with `k ≫ f = z ≫ q`. -/
private theorem comp_eq_of_pullback_snd_comp_eq_of_comp_eq
    {X' X W G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (q : G ⟶ X) (v : G ⟶ W) (w' : X' ⟶ W)
    (h : pullback.snd f q ≫ v = pullback.fst f q ≫ w') (z : H ⟶ G) (k : H ⟶ X')
    (hc : k ≫ f = z ≫ q) : z ≫ v = k ≫ w' := by
  simpa only [pullback.lift_snd_assoc, pullback.lift_fst_assoc] using
    congrArg (fun α => pullback.lift k z hc ≫ α) h

/-- The condition on `X' ×_X G` of a solution over `q : G ⟶ X` restricts along any `r : G' ⟶ G`. -/
theorem pullback_snd_comp_comp_eq_of_pullback_snd_comp_eq
    {X' X W G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (q : G ⟶ X) (r : G' ⟶ G) {q'' : G' ⟶ X} (hq : r ≫ q = q'') (v : G ⟶ W)
    (w' : X' ⟶ W) (h : pullback.snd f q ≫ v = pullback.fst f q ≫ w') :
    pullback.snd f q'' ≫ r ≫ v = pullback.fst f q'' ≫ w' := by
  subst hq
  rw [← Category.assoc]
  exact comp_eq_of_pullback_snd_comp_eq_of_comp_eq B S hS f q v w' h _ _
    (by rw [pullback.condition, Category.assoc])

/-- The condition on completions of a solution over `q : G ⟶ X` restricts along any
`r : G' ⟶ G`. -/
theorem completion_comp_eq_of_completion_eq {X W G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : G ⟶ X) (r : G' ⟶ G) {q'' : G' ⟶ X} (hq : r ≫ q = q'') (T : Set (points B S hS X))
    (v : G ⟶ W) (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (h : (completionSubfunctor B S hS G (pointsMap B S hS G q ⁻¹' T)).ι ≫
        Functor.whiskerRight v uliftFunctor.{u + 1} = completionMap B S hS q T ≫ ŵ) :
    (completionSubfunctor B S hS G' (pointsMap B S hS G' q'' ⁻¹' T)).ι ≫
        Functor.whiskerRight (r ≫ v) uliftFunctor.{u + 1} =
      completionMap B S hS q'' T ≫ ŵ := by
  subst hq
  have ha : pointsMap B S hS G' r '' (pointsMap B S hS G' (r ≫ q) ⁻¹' T) ⊆
      pointsMap B S hS G q ⁻¹' T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [Set.mem_preimage, pointsMap_comp, Function.comp_apply] using hx
  ext Zo y
  exact congrFun (congrArg (fun α => α.app Zo) h)
    ((completionSubfunctorMap B S hS r _ _ ha).app Zo y)

/-! ### Solutions over the open complement -/

/-- A morphism into `X'` lying over the open complement `U` of `T` is the composite of its image
in `U` with the inverse of the isomorphism `f⁻¹(U) ⟶ U`. -/
theorem eq_comp_inv_pullback_snd_comp_pullback_fst {X' X U H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (j : U ⟶ X) [IsIso (pullback.snd f j)] (l : H ⟶ X') (g : H ⟶ U)
    (h : l ≫ f = g ≫ j) :
    l = g ≫ inv (pullback.snd f j) ≫ pullback.fst f j := by
  have e : pullback.lift l g h = g ≫ inv (pullback.snd f j) := by
    rw [← cancel_mono (pullback.snd f j), pullback.lift_snd, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  rw [← Category.assoc, ← e, pullback.lift_fst]

/-- The section `U ⟶ X'` of `f` over the open complement `U`, composed with `f`, is the
inclusion of `U`. -/
theorem inv_pullback_snd_comp_pullback_fst_comp {X' X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (j : U ⟶ X) [IsIso (pullback.snd f j)] :
    inv (pullback.snd f j) ≫ pullback.fst f j ≫ f = j := by
  rw [pullback.condition, IsIso.inv_hom_id_assoc]

/-- A morphism out of `G` satisfying the condition on `X' ×_X G` of a solution over `q` is, on
every morphism `z` into `G` whose composite with `q` lies over `U`, the composite of the inverse
of `f⁻¹(U) ⟶ U` with `w'`. -/
theorem comp_eq_of_pullback_snd_comp_eq {X' X W G U H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (j : U ⟶ X) [IsIso (pullback.snd f j)] (q : G ⟶ X) (v : G ⟶ W)
    (w' : X' ⟶ W) (h : pullback.snd f q ≫ v = pullback.fst f q ≫ w')
    (z : H ⟶ G) (g : H ⟶ U) (hz : z ≫ q = g ≫ j) :
    z ≫ v = g ≫ inv (pullback.snd f j) ≫ pullback.fst f j ≫ w' := by
  have := comp_eq_of_pullback_snd_comp_eq_of_comp_eq B S hS f q v w' h z
    (g ≫ inv (pullback.snd f j) ≫ pullback.fst f j) (by
      rw [Category.assoc, Category.assoc, inv_pullback_snd_comp_pullback_fst_comp, hz])
  simpa only [Category.assoc] using this

/-- The range of the points of the section `q(y)` is the image of the range of the points of
`y`. -/
theorem range_pointsMap_yonedaEquiv_symm_app {G X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : G ⟶ X) (Zo : BigFppfOver B S hS) (y : G.obj (op Zo)) :
    Set.range (pointsMap B S hS (yoneda.obj Zo) (yonedaEquiv.symm (q.app (op Zo) y))) =
      pointsMap B S hS G q ''
        Set.range (pointsMap B S hS (yoneda.obj Zo) (yonedaEquiv.symm y)) := by
  rw [yonedaEquiv_symm_app, pointsMap_comp, Set.range_comp]

/-- **Solutions over the open complement.** If `q : G ⟶ X` factors through the open complement
`U` of `T`, then the composite of `G ⟶ U` with the inverse of `f⁻¹(U) ⟶ U` and with `w'` is a
solution over `q`. -/
theorem solution_of_factors_openSubspaceOfPoints_compl
    {X' X W G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : Set (points B S hS X)}
    (f : X' ⟶ X) [IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)]
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    (q : G ⟶ X) (g : G ⟶ (openSubspaceOfPoints B S hS X Tᶜ).toFunctor)
    (hg : g ≫ (openSubspaceOfPoints B S hS X Tᶜ).ι = q) :
    pullback.snd f q ≫ (g ≫ inv (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι) ≫
        pullback.fst f (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ w') = pullback.fst f q ≫ w' ∧
      (completionSubfunctor B S hS G (pointsMap B S hS G q ⁻¹' T)).ι ≫
        Functor.whiskerRight (g ≫ inv (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι) ≫
          pullback.fst f (openSubspaceOfPoints B S hS X Tᶜ).ι ≫ w') uliftFunctor.{u + 1} =
        completionMap B S hS q T ≫ ŵ := by
  set j := (openSubspaceOfPoints B S hS X Tᶜ).ι
  set k := g ≫ inv (pullback.snd f j) ≫ pullback.fst f j with hk
  have hkf : k ≫ f = q := by
    rw [hk, Category.assoc, Category.assoc, inv_pullback_snd_comp_pullback_fst_comp, hg]
  refine ⟨?_, ?_⟩
  · rw [eq_comp_inv_pullback_snd_comp_pullback_fst B S hS f j (pullback.fst f q)
      (pullback.snd f q ≫ g) (by rw [pullback.condition, Category.assoc, hg])]
    simp only [Category.assoc]
    rfl
  · have ha : pointsMap B S hS G k '' (pointsMap B S hS G q ⁻¹' T) ⊆
        pointsMap B S hS X' f ⁻¹' T := by
      rintro _ ⟨x, hx, rfl⟩
      have : pointsMap B S hS G q x = pointsMap B S hS X' f (pointsMap B S hS G k x) := by
        rw [← hkf, pointsMap_comp, Function.comp_apply]
      simpa only [Set.mem_preimage, ← this] using hx
    ext Zo y
    have h2 : (completionMap B S hS f T).app Zo
        ((completionSubfunctorMap B S hS k _ _ ha).app Zo y) =
        (completionMap B S hS q T).app Zo y := by
      apply Subtype.ext
      apply ULift.ext
      change f.app Zo (k.app Zo y.1.down) = q.app Zo y.1.down
      exact congrFun (congrArg (fun α => α.app Zo) hkf) y.1.down
    change _ = ŵ.app Zo ((completionMap B S hS q T).app Zo y)
    rw [← h2]
    exact (congrFun (congrArg (fun α => α.app Zo) hcompat)
      ((completionSubfunctorMap B S hS k _ _ ha).app Zo y)).symm

/-! ### Uniqueness of solutions -/

/-- A morphism of site objects whose underlying morphism of schemes has a property stable under
base change has that property after every representable base change. -/
theorem presheaf_yoneda_map (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    {V V' : BigFppfOver B S hS} (r : V ⟶ V') (hr : Q ((BigFppfOver.toScheme B S hS).map r)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B S hS))) (yoneda.map r) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ :
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  exact MorphismProperty.relative_map hr

/-- **Solutions are unique** (Stacks 0GI1). Over a site object `V` with a morphism `q` to `X`
whose underlying scheme is locally Noetherian, two solutions over `q` agree. -/
theorem eq_of_solution {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W)
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) [IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)]
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {V : BigFppfOver B S hS} [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (q : yoneda.obj V ⟶ X) (a b : yoneda.obj V ⟶ W)
    (ha₁ : pullback.snd f q ≫ a = pullback.fst f q ≫ w')
    (ha₂ : (completionSubfunctor B S hS (yoneda.obj V)
        (pointsMap B S hS (yoneda.obj V) q ⁻¹' T)).ι ≫
        Functor.whiskerRight a uliftFunctor.{u + 1} = completionMap B S hS q T ≫ ŵ)
    (hb₁ : pullback.snd f q ≫ b = pullback.fst f q ≫ w')
    (hb₂ : (completionSubfunctor B S hS (yoneda.obj V)
        (pointsMap B S hS (yoneda.obj V) q ⁻¹' T)).ι ≫
        Functor.whiskerRight b uliftFunctor.{u + 1} = completionMap B S hS q T ≫ ŵ) :
    a = b := by
  have hVnoeth : HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun V : Scheme.{u} => IsLocallyNoetherian V) := by
    have h1 := presheaf_yoneda_map B S hS (@Surjective.{u}) (𝟙 V)
      (by
        rw [CategoryTheory.Functor.map_id]
        infer_instance)
    have h2 := presheaf_yoneda_map B S hS (@Etale.{u}) (𝟙 V)
      (by
        rw [CategoryTheory.Functor.map_id]
        infer_instance)
    rw [CategoryTheory.Functor.map_id] at h1 h2
    exact ⟨V, 𝟙 _, h1, h2, inferInstance⟩
  refine eq_of_eq_on_compl_of_eq_on_completion B S hS (isAlgebraicSpace_yoneda B S hS V) hW
    hVnoeth (hT.preimage (continuous_pointsMap B S hS q)) a b ?_ (ha₂.trans hb₂.symm)
  set ιV := (openSubspaceOfPoints B S hS (yoneda.obj V)
    (pointsMap B S hS (yoneda.obj V) q ⁻¹' T)ᶜ).ι
  have hle : Subfunctor.range (ιV ≫ q) ≤ openSubspaceOfPoints B S hS X Tᶜ := by
    rintro Zo _ ⟨y, rfl⟩
    rw [mem_openSubspaceOfPoints_iff]
    change Set.range (pointsMap B S hS (yoneda.obj Zo.unop)
      (yonedaEquiv.symm (q.app (op Zo.unop) y.1))) ⊆ Tᶜ
    rw [range_pointsMap_yonedaEquiv_symm_app]
    rintro _ ⟨x, hx, rfl⟩
    exact y.2 hx
  set g := Subfunctor.lift (ιV ≫ q) hle
  have hg : ιV ≫ q = g ≫ (openSubspaceOfPoints B S hS X Tᶜ).ι := (Subfunctor.lift_ι _ _).symm
  rw [comp_eq_of_pullback_snd_comp_eq B S hS f _ q a w' ha₁ ιV g hg,
    comp_eq_of_pullback_snd_comp_eq B S hS f _ q b w' hb₁ ιV g hg]

/-! ### Being a solution is local -/

/-- A section of a representable presheaf has point-set image in the inverse image of `T'` under
`q` exactly when every point of the corresponding morphism maps into `T'`. -/
theorem hasImageIn_yoneda_iff {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V Zo : BigFppfOver B S hS}
    (q : yoneda.obj V ⟶ G) (T' : Set (points B S hS G)) (h₀ : Zo ⟶ V) :
    HasImageIn B S hS (yoneda.obj V) (pointsMap B S hS _ q ⁻¹' T') Zo h₀ ↔
      ∀ z, pointsMap B S hS _ (yoneda.map h₀ ≫ q) z ∈ T' := by
  have e : yonedaEquiv.symm h₀ = yoneda.map h₀ :=
    yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])
  rw [hasImageIn_iff_range_subset, e, Set.range_subset_iff, pointsMap_comp]
  rfl

/-- Two morphisms from a representable presheaf to an algebraic space agreeing on the members of
a covering sieve agree. -/
theorem hom_ext_of_sieve {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) {Zo : BigFppfOver B S hS} (R : Sieve Zo)
    (hR : R ∈ BigFppfOver.topology B S hS Zo) {c d : yoneda.obj Zo ⟶ W}
    (h : ∀ ⦃Y : BigFppfOver B S hS⦄ ⦃g : Y ⟶ Zo⦄, R.arrows g →
      yoneda.map g ≫ c = yoneda.map g ≫ d) :
    c = d := by
  have hsep := (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp
    hW.isSheaf) R hR).isSeparatedFor
  refine yonedaEquiv.injective (hsep.ext fun Y g hg => ?_)
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality, h hg]

/-- **Being a solution is local.** A morphism `a` out of a site object `V` is a solution over
`q : V ⟶ X` as soon as its restrictions to the members of a covering sieve of `V` are solutions
over the restrictions of `q`. -/
theorem solution_of_sieve {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) {T : Set (points B S hS X)} (f : X' ⟶ X) (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {V : BigFppfOver B S hS} (q : yoneda.obj V ⟶ X) (a : yoneda.obj V ⟶ W)
    (R : Sieve V) (hR : R ∈ BigFppfOver.topology B S hS V)
    (hloc : ∀ ⦃Y : BigFppfOver B S hS⦄ ⦃g : Y ⟶ V⦄, R.arrows g →
      pullback.snd f (yoneda.map g ≫ q) ≫ yoneda.map g ≫ a =
          pullback.fst f (yoneda.map g ≫ q) ≫ w' ∧
        (completionSubfunctor B S hS (yoneda.obj Y)
          (pointsMap B S hS _ (yoneda.map g ≫ q) ⁻¹' T)).ι ≫
          Functor.whiskerRight (yoneda.map g ≫ a) uliftFunctor.{u + 1} =
          completionMap B S hS (yoneda.map g ≫ q) T ≫ ŵ) :
    pullback.snd f q ≫ a = pullback.fst f q ≫ w' ∧
      (completionSubfunctor B S hS (yoneda.obj V) (pointsMap B S hS _ q ⁻¹' T)).ι ≫
        Functor.whiskerRight a uliftFunctor.{u + 1} = completionMap B S hS q T ≫ ŵ := by
  have hsep : ∀ {Zo : BigFppfOver B S hS} (R' : Sieve Zo),
      R' ∈ BigFppfOver.topology B S hS Zo → Presieve.IsSeparatedFor W R'.arrows :=
    fun R' hR' => (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp
      hW.isSheaf) R' hR').isSeparatedFor
  refine ⟨?_, ?_⟩
  · have key : ∀ (Zo : BigFppfOver B S hS) (e : yoneda.obj Zo ⟶ pullback f q),
        e ≫ pullback.snd f q ≫ a = e ≫ pullback.fst f q ≫ w' := by
      intro Zo e
      obtain ⟨h₀, hh₀⟩ := yoneda.map_surjective (e ≫ pullback.snd f q)
      refine hom_ext_of_sieve B S hS hW (R.pullback h₀)
        ((BigFppfOver.topology B S hS).pullback_stable h₀ hR) fun Y g hg => ?_
      obtain ⟨h1, -⟩ := hloc hg
      have hc : (yoneda.map g ≫ e ≫ pullback.fst f q) ≫ f =
          𝟙 _ ≫ yoneda.map (g ≫ h₀) ≫ q := by
        rw [Category.assoc, Category.assoc, pullback.condition, Category.id_comp,
          Functor.map_comp, Category.assoc, ← Category.assoc e, ← hh₀]
      have h2 := comp_eq_of_pullback_snd_comp_eq_of_comp_eq B S hS f _ _ w' h1 _ _ hc
      simp only [Category.id_comp, Category.assoc] at h2
      rw [Functor.map_comp, Category.assoc, hh₀] at h2
      simpa only [Category.assoc] using h2
    exact hom_ext_yoneda fun Zo e => by simpa only [Category.assoc] using key Zo e
  · ext Zo y
    apply ULift.ext
    obtain ⟨⟨h₀⟩, hy⟩ := y
    have hT : ∀ z, pointsMap B S hS _ (yoneda.map h₀ ≫ q) z ∈ T :=
      (hasImageIn_yoneda_iff B S hS q T h₀).mp hy
    refine (hsep (R.pullback h₀) ((BigFppfOver.topology B S hS).pullback_stable h₀ hR)).ext
      fun Y g hg => ?_
    obtain ⟨-, h2⟩ := hloc hg
    have hmem : HasImageIn B S hS (yoneda.obj Y)
        (pointsMap B S hS _ (yoneda.map (g ≫ h₀) ≫ q) ⁻¹' T) Y (𝟙 Y) := by
      rw [hasImageIn_yoneda_iff]
      intro z
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc,
        pointsMap_comp, Function.comp_apply]
      exact hT _
    have h3' := congrFun (congrArg (fun α => α.app (op Y)) h2) ⟨ULift.up (𝟙 Y), hmem⟩
    have h3 := congrArg ULift.down h3'
    have hn1 : W.map g.op (a.app (op Zo.unop) h₀) = a.app (op Y) (g ≫ h₀) :=
      (NatTrans.naturality_apply a g.op h₀).symm
    have hn2 := congrArg ULift.down (NatTrans.naturality_apply ŵ g.op
      ((completionMap B S hS q T).app (op Zo.unop) ⟨⟨h₀⟩, hy⟩))
    change W.map g.op (a.app (op Zo.unop) h₀) = W.map g.op
      (ŵ.app (op Zo.unop) ((completionMap B S hS q T).app (op Zo.unop) ⟨⟨h₀⟩, hy⟩)).down
    have hl : (yoneda.map (g ≫ h₀) ≫ a).app (op Y) (𝟙 Y) = a.app (op Y) (g ≫ h₀) := by
      simp
    have he : (completionMap B S hS (yoneda.map (g ≫ h₀) ≫ q) T).app (op Y)
        ⟨ULift.up (𝟙 Y), hmem⟩ = (completionSubfunctor B S hS X T).toFunctor.map g.op
          ((completionMap B S hS q T).app (op Zo.unop) ⟨⟨h₀⟩, hy⟩) := by
      apply Subtype.ext
      apply ULift.ext
      change q.app (op Y) (𝟙 Y ≫ g ≫ h₀) = X.map g.op (q.app (op Zo.unop) h₀)
      rw [Category.id_comp]
      exact (NatTrans.naturality_apply q g.op h₀)
    rw [hn1, ← hl]
    refine h3.trans (Eq.trans ?_ hn2)
    change (ŵ.app (op Y) ((completionMap B S hS (yoneda.map (g ≫ h₀) ≫ q) T).app (op Y)
      ⟨ULift.up (𝟙 Y), hmem⟩)).down = _
    rw [he]

/-! ### From an atlas to the whole space -/

/-- **A solution over a surjective étale atlas is a solution over `X`.** If `p : V ⟶ X` is a
surjective étale atlas and `w : X ⟶ W` is such that `p ≫ w` is a solution over `p`, then `w` is
sent to `(w', ŵ)` by the comparison map of Stacks 0GI3. -/
theorem morToModificationCompletion_eq_of_solution_atlas {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W) {T : Set (points B S hS X)} (f : X' ⟶ X) (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {Va : BigFppfOver B S hS} (p : yoneda.obj Va ⟶ X)
    (hpsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (w : X ⟶ W) (h₁ : pullback.snd f p ≫ p ≫ w = pullback.fst f p ≫ w')
    (h₂ : (completionSubfunctor B S hS (yoneda.obj Va) (pointsMap B S hS _ p ⁻¹' T)).ι ≫
        Functor.whiskerRight (p ≫ w) uliftFunctor.{u + 1} = completionMap B S hS p T ≫ ŵ) :
    morToModificationCompletion B S hS f T W w = (w', ŵ) := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  refine Prod.ext ?_ ?_
  · -- the comparison with `w'`, on an atlas of `X' ×_X V`
    change f ≫ w = w'
    have hPB := isAlgebraicSpace_pullback B S hS f p hX' (isAlgebraicSpace_yoneda B S hS Va) hX
    obtain ⟨Vb, a, has, hae⟩ := hPB.exists_atlas
    have hfs := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f p).flip hpsurj
    have hfe := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f p).flip hpet
    refine hom_ext_of_etale_atlas B S hS hX'.isSheaf hW.isSheaf (a ≫ pullback.fst f p)
      (MorphismProperty.comp_mem _ _ _ has hfs) (MorphismProperty.comp_mem _ _ _ hae hfe) ?_
    simp only [Category.assoc]
    rw [pullback.condition_assoc, h₁]
  · -- the comparison with `ŵ`, on sections, after the base change of the atlas
    change (completionSubfunctor B S hS X T).ι ≫ Functor.whiskerRight w uliftFunctor.{u + 1} = ŵ
    ext Zo y
    have hx := y.2
    set x := y.1.down with hxdef
    set g : yoneda.obj Zo.unop ⟶ X := yonedaEquiv.symm x with hg
    have hrep := hpet.rep
    set r := hrep.snd g
    set s := hrep.fst' g
    have hw : yoneda.map s ≫ p = yoneda.map r ≫ g := (hrep.isPullback' g).w
    have hrs : Surjective ((BigFppfOver.toScheme B S hS).map r) := hpsurj.property_snd g
    have hre : Etale ((BigFppfOver.toScheme B S hS).map r) := hpet.property_snd g
    have hxT : Set.range (pointsMap B S hS _ g) ⊆ T := by
      rwa [hg, ← hasImageIn_iff_range_subset]
    have hmem : HasImageIn B S hS (yoneda.obj Va) (pointsMap B S hS _ p ⁻¹' T)
        (hrep.pullback g) s := by
      rw [hasImageIn_yoneda_iff]
      intro z
      rw [hw, pointsMap_comp, Function.comp_apply]
      exact hxT ⟨_, rfl⟩
    have h3' := congrFun (congrArg (fun α => α.app (op (hrep.pullback g))) h₂) ⟨ULift.up s, hmem⟩
    have h3 := congrArg ULift.down h3'
    have hcd : g ≫ w = yonedaEquiv.symm (ŵ.app Zo y).down := by
      refine hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS Zo.unop).isSheaf
        hW.isSheaf (yoneda.map r) (presheaf_yoneda_map B S hS _ r hrs)
        (presheaf_yoneda_map B S hS _ r hre) ?_
      apply yonedaEquiv.injective
      rw [← Category.assoc, ← hw, ← yonedaEquiv_naturality, Equiv.apply_symm_apply,
        Category.assoc, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      have hn := congrArg ULift.down (NatTrans.naturality_apply ŵ r.op y)
      refine h3.trans (Eq.trans ?_ hn)
      change (ŵ.app (op (hrep.pullback g)) ((completionMap B S hS p T).app
        (op (hrep.pullback g)) ⟨ULift.up s, hmem⟩)).down = _
      have he : (completionMap B S hS p T).app (op (hrep.pullback g)) ⟨ULift.up s, hmem⟩ =
          (completionSubfunctor B S hS X T).toFunctor.map r.op y := by
        apply Subtype.ext
        apply ULift.ext
        change p.app _ s = X.map r.op x
        have h4 := congrArg yonedaEquiv hw
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality] at h4
        exact h4.trans (congrArg (X.map r.op) (Equiv.apply_symm_apply yonedaEquiv x))
      rw [he]
    apply ULift.ext
    have h5 := congrArg yonedaEquiv hcd
    rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h5

/-! ### Gluing local solutions -/

/-- A morphism all of whose points lie in `T'` factors through the subfunctor cut out by
`T'`. -/
theorem range_le_openSubspaceOfPoints_of_range_subset {G X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : G ⟶ X) (T' : Set (points B S hS X)) (h : Set.range (pointsMap B S hS G q) ⊆ T') :
    Subfunctor.range q ≤ openSubspaceOfPoints B S hS X T' := by
  rintro Zo _ ⟨y, rfl⟩
  rw [mem_openSubspaceOfPoints_iff]
  change Set.range (pointsMap B S hS (yoneda.obj Zo.unop)
    (yonedaEquiv.symm (q.app (op Zo.unop) y))) ⊆ T'
  rw [range_pointsMap_yonedaEquiv_symm_app]
  rintro _ ⟨x, -, rfl⟩
  exact h ⟨x, rfl⟩

/-- Two solutions over `q₁` and `q₂` agree after composing with `s` and `t`, where `s ≫ q₁` and
`t ≫ q₂` agree and the source of `s` and `t` is locally Noetherian. -/
private theorem comp_eq_comp_of_solution {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) [IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)]
    (w' : X' ⟶ W) (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    {V₁ V₂ Q : BigFppfOver B S hS} [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Q)]
    (q₁ : yoneda.obj V₁ ⟶ X) (q₂ : yoneda.obj V₂ ⟶ X) (v₁ : yoneda.obj V₁ ⟶ W)
    (v₂ : yoneda.obj V₂ ⟶ W) (s : Q ⟶ V₁) (t : Q ⟶ V₂)
    (hq : yoneda.map t ≫ q₂ = yoneda.map s ≫ q₁)
    (h₁ : pullback.snd f q₁ ≫ v₁ = pullback.fst f q₁ ≫ w' ∧
      (completionSubfunctor B S hS (yoneda.obj V₁) (pointsMap B S hS _ q₁ ⁻¹' T)).ι ≫
        Functor.whiskerRight v₁ uliftFunctor.{u + 1} = completionMap B S hS q₁ T ≫ ŵ)
    (h₂ : pullback.snd f q₂ ≫ v₂ = pullback.fst f q₂ ≫ w' ∧
      (completionSubfunctor B S hS (yoneda.obj V₂) (pointsMap B S hS _ q₂ ⁻¹' T)).ι ≫
        Functor.whiskerRight v₂ uliftFunctor.{u + 1} = completionMap B S hS q₂ T ≫ ŵ) :
    yoneda.map s ≫ v₁ = yoneda.map t ≫ v₂ :=
  eq_of_solution B S hS hW hT f w' ŵ _ _ _
    (pullback_snd_comp_comp_eq_of_pullback_snd_comp_eq B S hS f _ _ rfl _ w' h₁.1)
    (completion_comp_eq_of_completion_eq B S hS _ _ rfl T _ ŵ h₁.2)
    (pullback_snd_comp_comp_eq_of_pullback_snd_comp_eq B S hS f _ _ hq _ w' h₂.1)
    (completion_comp_eq_of_completion_eq B S hS _ _ hq T _ ŵ h₂.2)

/-- **The existence half of Stacks 0GI3 is étale local.** Let `X` be a locally Noetherian
algebraic space over `S` with a surjective étale atlas `p : V ⟶ X`, let `T ⊆ |X|` be closed with
open complement `U`, let `f : X' ⟶ X` be a morphism of algebraic spaces whose base change
`f⁻¹(U) ⟶ U` is an isomorphism, and let `(w', ŵ)` be a compatible pair of morphisms
`X' ⟶ W`, `X_{/T} ⟶ W` to an algebraic space `W`. Suppose that every point of `V` over `T` lies
in the image of an étale morphism `r : P ⟶ V` of site objects over which a solution exists, that
is, a morphism `P ⟶ W` restricting to the base changes of `w'` and of `ŵ`. Then there is a
morphism `w : X ⟶ W` restricting to `w'` on `X'` and to `ŵ` on `X_{/T}`. -/
theorem exists_morToModificationCompletion_eq_of_etale_local
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1})
    {Va : BigFppfOver B S hS} (p : yoneda.obj Va ⟶ X)
    (hpsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hpet : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hloc : ∀ v : points B S hS (yoneda.obj Va), pointsMap B S hS _ p v ∈ T →
      ∃ (P : BigFppfOver B S hS) (r : P ⟶ Va), Etale ((BigFppfOver.toScheme B S hS).map r) ∧
        pointsToScheme B S hS Va v ∈ Set.range ((BigFppfOver.toScheme B S hS).map r).base ∧
        ∃ wP : yoneda.obj P ⟶ W,
          pullback.snd f (yoneda.map r ≫ p) ≫ wP = pullback.fst f (yoneda.map r ≫ p) ≫ w' ∧
          (completionSubfunctor B S hS (yoneda.obj P)
            (pointsMap B S hS _ (yoneda.map r ≫ p) ⁻¹' T)).ι ≫
            Functor.whiskerRight wP uliftFunctor.{u + 1} =
            completionMap B S hS (yoneda.map r ≫ p) T ≫ ŵ) :
    ∃ w : X ⟶ W, morToModificationCompletion B S hS f T W w = (w', ŵ) := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  set j := (openSubspaceOfPoints B S hS X Tᶜ).ι
  have hnoeth := (exists_atlas_iff_forall_etale B S hS X
    (fun V : Scheme.{u} => IsLocallyNoetherian V) hX).mp hXnoeth
  have hetcomp : ∀ {P : BigFppfOver B S hS} (r : P ⟶ Va),
      Etale ((BigFppfOver.toScheme B S hS).map r) →
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map r ≫ p) :=
    fun r hr => MorphismProperty.comp_mem _ _ _ (presheaf_yoneda_map B S hS _ r hr) hpet
  -- the scheme points of the atlas over `T`
  obtain ⟨Ws, hWsmem, hWsclosed⟩ :
      ∃ Ws : Set ((BigFppfOver.toScheme B S hS).obj Va),
        (∀ v : points B S hS (yoneda.obj Va),
          (pointsToScheme B S hS Va v ∈ Ws ↔ pointsMap B S hS (yoneda.obj Va) p v ∈ T)) ∧
          IsClosed Ws := by
    refine ⟨pointsToScheme B S hS Va '' (pointsMap B S hS (yoneda.obj Va) p ⁻¹' T), ?_, ?_⟩
    · intro v
      refine ⟨?_, fun hv => ⟨v, hv, rfl⟩⟩
      rintro ⟨v', hv', hveq⟩
      rw [← injective_pointsToScheme B S hS Va hveq]
      exact hv'
    · exact (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS Va _).mp
        (hT.preimage (continuous_pointsMap B S hS p))
  -- the open part of the atlas over `U`, with its solution
  let Uo : ((BigFppfOver.toScheme B S hS).obj Va).Opens := ⟨Wsᶜ, hWsclosed.isOpen_compl⟩
  let PU := monoSiteObj B S hS Uo.ι
  let rU : PU ⟶ Va := monoSiteHom B S hS Uo.ι
  have hrUet : Etale ((BigFppfOver.toScheme B S hS).map rU) := by
    change Etale Uo.ι
    infer_instance
  have hUle : Subfunctor.range (yoneda.map rU ≫ p) ≤ openSubspaceOfPoints B S hS X Tᶜ := by
    refine range_le_openSubspaceOfPoints_of_range_subset B S hS _ _ ?_
    rintro _ ⟨z, rfl⟩ hzT
    rw [pointsMap_comp, Function.comp_apply, ← hWsmem] at hzT
    have hz := pointsToScheme_pointsMap_yoneda B S hS rU z
    rw [hz] at hzT
    have hmemU : ((BigFppfOver.toScheme B S hS).map rU) (pointsToScheme B S hS PU z) ∈
        (Uo : Set ((BigFppfOver.toScheme B S hS).obj Va)) := by
      have key : ∀ y : Uo.toScheme, Uo.ι y ∈ (Uo : Set _) := fun y => by
        rw [← Scheme.Opens.range_ι]
        exact ⟨y, rfl⟩
      exact key (pointsToScheme B S hS PU z)
    exact hmemU hzT
  set gU := Subfunctor.lift (yoneda.map rU ≫ p) hUle
  obtain ⟨hU₁, hU₂⟩ := solution_of_factors_openSubspaceOfPoints_compl B S hS f w' ŵ hcompat
    (yoneda.map rU ≫ p) gU (Subfunctor.lift_ι _ _)
  -- the covering family of the atlas
  choose P r hr hrange wP hw₁ hw₂ using hloc
  let I := Option {v : points B S hS (yoneda.obj Va) // pointsMap B S hS _ p v ∈ T}
  let Pf : I → BigFppfOver B S hS := fun i => match i with
    | none => PU
    | some v => P v.1 v.2
  let rf : ∀ i, Pf i ⟶ Va := fun i => match i with
    | none => rU
    | some v => r v.1 v.2
  let wf : ∀ i, yoneda.obj (Pf i) ⟶ W := fun i => match i with
    | none => gU ≫ inv (pullback.snd f j) ≫ pullback.fst f j ≫ w'
    | some v => wP v.1 v.2
  have hrf : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (rf i)) := by
    rintro (_ | v)
    exacts [hrUet, hr v.1 v.2]
  have hwf : ∀ i, (pullback.snd f (yoneda.map (rf i) ≫ p) ≫ wf i =
        pullback.fst f (yoneda.map (rf i) ≫ p) ≫ w') ∧
      (completionSubfunctor B S hS (yoneda.obj (Pf i))
        (pointsMap B S hS _ (yoneda.map (rf i) ≫ p) ⁻¹' T)).ι ≫
        Functor.whiskerRight (wf i) uliftFunctor.{u + 1} =
        completionMap B S hS (yoneda.map (rf i) ≫ p) T ≫ ŵ := by
    rintro (_ | v)
    · exact ⟨hU₁, hU₂⟩
    · exact ⟨hw₁ v.1 v.2, hw₂ v.1 v.2⟩
  have hcov : Sieve.generate (Presieve.ofArrows Pf rf) ∈ BigFppfOver.topology B S hS Va := by
    have hflat : ∀ i, Flat (B.inclusion.map (rf i).left) := fun i => by
      have := hrf i
      change Flat ((BigFppfOver.toScheme B S hS).map (rf i))
      infer_instance
    have hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (rf i).left) := fun i => by
      have := hrf i
      change LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (rf i))
      infer_instance
    have hsurj : ∀ x : (B.inclusion.obj Va.left),
        ∃ i, x ∈ Set.range (B.inclusion.map (rf i).left) := by
      intro x
      obtain ⟨v, rfl⟩ := surjective_pointsToScheme B S hS Va x
      by_cases hv : pointsMap B S hS _ p v ∈ T
      · exact ⟨some ⟨v, hv⟩, hrange v hv⟩
      · refine ⟨none, ⟨⟨pointsToScheme B S hS Va v, ?_⟩, rfl⟩⟩
        change pointsToScheme B S hS Va v ∈ Wsᶜ
        rwa [Set.mem_compl_iff, hWsmem]
    refine GrothendieckTopology.superset_covering _ ?_
      (mem_topology_of_family B S hS (fun i => (Pf i).left) (fun i => (rf i).left)
        hflat hlfp hsurj)
    rintro Y g ⟨Z, a, b, ⟨i⟩, rfl⟩
    refine ⟨Pf i, a ≫ Over.homMk (𝟙 (Pf i).left) (by simp), rf i, ⟨i⟩, ?_⟩
    ext
    simp
  -- gluing the local solutions on the atlas
  have hsh : Presieve.IsSheafFor W (Presieve.ofArrows Pf rf) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp hW.isSheaf) _ hcov)
  have hagree : ∀ i i', yoneda.map (pullback.fst (rf i) (rf i')) ≫ wf i =
      yoneda.map (pullback.snd (rf i) (rf i')) ≫ wf i' := by
    intro i i'
    set Q := pullback (rf i) (rf i')
    have hfst : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst (rf i) (rf i'))) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        ((IsPullback.of_hasPullback (rf i) (rf i')).map (BigFppfOver.toScheme B S hS)).flip
        (hrf i')
    have hq : yoneda.map (pullback.snd (rf i) (rf i')) ≫ yoneda.map (rf i') ≫ p =
        yoneda.map (pullback.fst (rf i) (rf i')) ≫ yoneda.map (rf i) ≫ p := by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition]
    have hQnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Q) := by
      refine hnoeth Q (yoneda.map (pullback.fst (rf i) (rf i')) ≫ yoneda.map (rf i) ≫ p) ?_
      have := hetcomp _ (show Etale ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (rf i) (rf i') ≫ rf i)) by
          rw [Functor.map_comp]; have := hrf i; infer_instance)
      rwa [Functor.map_comp, Category.assoc] at this
    exact comp_eq_comp_of_solution B S hS hW hT f w' ŵ _ _ _ _ _ _ hq (hwf i) (hwf i')
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsh
    (fun i => yonedaEquiv (wf i)) (by
      intro i i' Z gi gi' hgi
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      congr 1
      obtain ⟨L, hL, hL'⟩ : ∃ L : Z ⟶ pullback (rf i) (rf i'),
          L ≫ pullback.fst _ _ = gi ∧ L ≫ pullback.snd _ _ = gi' :=
        ⟨_, pullback.lift_fst gi gi' hgi, pullback.lift_snd gi gi' hgi⟩
      rw [← hL, ← hL', Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        hagree])
  set wVa : yoneda.obj Va ⟶ W := yonedaEquiv.symm t
  have hwVa : ∀ i, yoneda.map (rf i) ≫ wVa = wf i := fun i =>
    yonedaEquiv.injective (by rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, ht])
  -- the glued morphism is a solution over the atlas
  obtain ⟨hV₁, hV₂⟩ := solution_of_sieve B S hS hW f w' ŵ p wVa _ hcov (by
    rintro Y g ⟨Z, h, _, ⟨i⟩, rfl⟩
    have hq : yoneda.map h ≫ yoneda.map (rf i) ≫ p = yoneda.map (h ≫ rf i) ≫ p := by
      rw [Functor.map_comp, Category.assoc]
    have e : yoneda.map (h ≫ rf i) ≫ wVa = yoneda.map h ≫ wf i := by
      rw [Functor.map_comp, Category.assoc, hwVa]
    rw [e]
    exact ⟨pullback_snd_comp_comp_eq_of_pullback_snd_comp_eq B S hS f _ _ hq _ w' (hwf i).1,
      completion_comp_eq_of_completion_eq B S hS _ _ hq T _ ŵ (hwf i).2⟩)
  -- descending to `X`
  obtain ⟨w, hw, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hX.isSheaf hW.isSheaf p
    hpsurj hpet wVa (by
      intro R s t hR
      have hs := MorphismProperty.IsStableUnderBaseChange.of_isPullback hR.flip hpet
      have hRnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj R) :=
        hnoeth R _ (MorphismProperty.comp_mem _ _ _ hs hpet)
      exact comp_eq_comp_of_solution B S hS hW hT f w' ŵ _ _ _ _ _ _ hR.w.symm
        ⟨hV₁, hV₂⟩ ⟨hV₁, hV₂⟩)
  exact ⟨w, morToModificationCompletion_eq_of_solution_atlas B S hS hX hX' hW f w' ŵ p
    hpsurj hpet w (by rwa [hw]) (by rwa [hw])⟩

end Space

end AlgebraicGeometry

end
