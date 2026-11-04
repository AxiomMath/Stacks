module

public import StacksFrontier.Algebra.Homology.RightDerivedEdge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeComposition

/-!
# The calculus of the edge morphism of a composite of right derived functors

`StacksFrontier/Algebra/Homology/RightDerivedEdge.lean` constructs, for additive functors
`P : A ⥤ B` and `Q : B ⥤ D` with `P` preserving injective objects and *no* exactness hypothesis
on `P`, the edge morphism

`Stacks.Cohomology.RightDerivedEdge.edge P Q n : P ⋙ Qⁿ ⟶ (P ⋙ Q)ⁿ`

of the Grothendieck spectral sequence of the pair, and characterises it by
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq`: any augmentation-preserving comparison of any
injective resolutions computes it.

This file is the calculus of that morphism: how it behaves under composition in the first
variable, under a natural transformation of the second variable, under a natural transformation of
the first variable, and when the first variable is exact.

In the geometric reading `P = f_*` and `Q = Γ(Y, -)`, so that `edge` is the pullback map
`Hⁿ(Y, f_* F) ⟶ Hⁿ(X, F)` on sheaf cohomology, the four results say: the pullback along a
composite of morphisms is the composite of the pullbacks; the pullback commutes with a change of
the sections functor; the pullback is compatible with an isomorphism of the direct-image functors,
which is what a base-change square of sites supplies; and the pullback along a morphism whose
direct image is *exact* — for instance the restriction along the inclusion of a dense subsite — is
an isomorphism.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.edge_app_comp` — **the edge morphism of a composite.**
  `edge (P₂ ⋙ P₁) Q n` at `W` is `edge P₁ Q n` at `P₂ W` followed by `edge P₂ (P₁ ⋙ Q) n` at `W`.
* `Stacks.Cohomology.RightDerivedEdge.edge_app_comp_rightDerived_whiskerLeft` — **compatibility
  with a natural transformation of the target functor.**
* `Stacks.Cohomology.RightDerivedEdge.map_comp_edge_app` — **compatibility with a natural
  transformation of the source functor**: for `ρ : P ⟶ P'`, the square relating `edge P Q n` and
  `edge P' Q n` across `ρ` commutes. This is the one that consumes a base-change square.
* `Stacks.Cohomology.RightDerivedEdge.isIso_edge_app` — **the edge morphism of an exact functor
  preserving injectives is an isomorphism.** This is Stacks 015Z read on one object: `P` carries an
  injective resolution to an injective resolution, so the comparison may be taken to be the
  identity.

## Implementation notes

Every proof runs through `edge_app_eq` at explicitly chosen resolutions and comparisons, together
with `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality` and
`CategoryTheory.InjectiveResolution.rightDerived_app_eq` for the two other kinds of map that
appear. The only step that is not an identity of cochain maps is in `map_comp_edge_app`, where two
comparisons agreeing on the augmentation have to be identified; that is
`Stacks.Cohomology.RightDerivedEdge.homologyMap_map_eq_of_aug`, and it is the only place a
homotopy enters.

The augmentation of an injective resolution of `X` has source `((single₀ _).obj X).X 0` rather
than `X`, so composites involving it are only definitionally type-correct and the rewriting
tactics cannot be applied to them. As in `RightDerivedEdge.lean`, the chases are therefore
isolated in statements over *variable* objects — `comp_comp_eq` here, and `map_comp_eq_map` there
— which can be applied by `exact`.

`(P₂ ⋙ P₁).mapHomologicalComplex c` and `P₁.mapHomologicalComplex c ⋙ P₂.mapHomologicalComplex c`
agree by definition but not syntactically, as the module documentation of `RightDerivedEdge.lean`
already notes; `mapHomologicalComplex_map_mapHomologicalComplex_map` and
`mapHomologicalComplex_map_natTrans_app` are definitional restatements for the rewriting tactics
(the first is the one `edge_app_comp` rewrites with). For the same reason the composites at the
end of the four main proofs pass through objects spelled in two definitionally equal ways —
`K.homology n` against `(HomologicalComplex.homologyFunctor _ _ n).obj K`, or
`(P ⋙ Q).mapHomologicalComplex c` against the iterated image — so at the transparency `rw` and
`simp` use they are not type-correct and can be neither reassociated nor cancelled. The closing
cancellations are therefore again isolated in statements over variable objects
(`comp_comp_inv_hom_comp`, `comp_inv_hom_comp_eq`, `comp_comp_eq_comp_inv_hom`,
`comp_comp_eq_comp_of_eq_id`), which `exact` applies by unifying at default transparency; for the
same reason the instance in `isIso_edge_app` is supplied by `IsIso.comp_isIso'` rather than found
by instance search.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.Cohomology.RightDerivedEdge

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ] [HasInjectiveResolutions ℬ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [Abelian 𝒞] [HasInjectiveResolutions 𝒞]
  {ℰ : Type u₄} [Category.{v₄} ℰ] [Abelian ℰ]

omit [HasInjectiveResolutions 𝒜] [HasInjectiveResolutions ℬ] in
/-- Applying `Q` termwise to the termwise image of a cochain map under `P` is applying `P ⋙ Q`
termwise to it. The two sides are definitionally equal; this is the restatement the rewriting
tactics can use. -/
theorem mapHomologicalComplex_map_mapHomologicalComplex_map (P : ℬ ⥤ 𝒜) [P.Additive]
    (Q : 𝒜 ⥤ ℰ) [Q.Additive] {K L : CochainComplex ℬ ℕ} (f : K ⟶ L) :
    (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map f) =
      ((P ⋙ Q).mapHomologicalComplex (ComplexShape.up ℕ)).map f :=
  rfl

omit [HasInjectiveResolutions 𝒜] [HasInjectiveResolutions ℬ] in
/-- Applying `Q` termwise to the termwise image of a natural transformation of the source is
whiskering that transformation with `Q`. The two sides are definitionally equal; this is the
restatement the rewriting tactics can use. -/
theorem mapHomologicalComplex_map_natTrans_app {P P' : ℬ ⥤ 𝒜} [P.Additive] [P'.Additive]
    (ρ : P ⟶ P') (Q : 𝒜 ⥤ ℰ) [Q.Additive] (K : CochainComplex ℬ ℕ) :
    (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex ρ (ComplexShape.up ℕ)).app K) =
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight ρ Q) (ComplexShape.up ℕ)).app K :=
  rfl

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The augmentation chase used below: from `i ≫ a = j` and `j ≫ b = k` one gets
`i ≫ a ≫ b = k`. Stated over variable objects, because at the concrete data of interest the
source of `i` is the degree-zero term of a single complex and the composites are only
definitionally type-correct, so the rewriting tactics cannot be applied to them while this
statement can be applied by `exact`. -/
theorem comp_comp_eq {W V V' U : 𝒜} (i : W ⟶ V) (a : V ⟶ V') (b : V' ⟶ U) (j : W ⟶ V')
    (k : W ⟶ U) (ha : i ≫ a = j) (hb : j ≫ b = k) : i ≫ a ≫ b = k := by
  rw [← Category.assoc, ha, hb]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The variant of `comp_comp_eq` in which the first chase lands on a composite. Stated over
variable objects for the same reason. -/
theorem comp_comp_eq_assoc {W U V V' T : 𝒜} (i : W ⟶ V) (a : V ⟶ V') (b : V' ⟶ T) (r : W ⟶ U)
    (j : U ⟶ V') (k : U ⟶ T) (ha : i ≫ a = r ≫ j) (hb : j ≫ b = k) : i ≫ a ≫ b = r ≫ k := by
  rw [← Category.assoc, ha, Category.assoc, hb]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The variant of `comp_comp_eq` in which the second chase lands on a composite. Stated over
variable objects for the same reason. -/
theorem comp_comp_eq_of_eq {W V V' U T : 𝒜} (i : W ⟶ V) (a : V ⟶ V') (b : V' ⟶ T) (d : W ⟶ V')
    (r : W ⟶ U) (k : U ⟶ T) (ha : i ≫ a = d) (hb : d ≫ b = r ≫ k) : i ≫ a ≫ b = r ≫ k := by
  rw [← Category.assoc, ha, hb]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The cancellation closing `edge_app_comp`: an inverse followed by the corresponding forward
map, inserted in the middle of a composite, cancels. Stated over variable objects, because at the
concrete data of interest the objects on the two sides of the cancelling pair are spelled
differently (definitionally but not syntactically), so the rewriting tactics cannot reassociate
the composites while this statement can be applied by `exact`. -/
private theorem comp_comp_inv_hom_comp {W V V' U T S : 𝒜} (a : W ⟶ V) (b : V ⟶ V') (c : V' ⟶ T)
    (e : U ≅ V') (k : T ⟶ S) : a ≫ (b ≫ c) ≫ k = a ≫ (b ≫ e.inv) ≫ e.hom ≫ c ≫ k := by
  simp

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The cancellation closing `edge_app_comp_rightDerived_whiskerLeft`: two inverse-forward pairs
cancel and the remaining square is `h`. Stated over variable objects for the same reason as
`comp_comp_inv_hom_comp`. -/
private theorem comp_inv_hom_comp_eq {W V V' U U' T S : 𝒜} (f : W ⟶ V) (e : U ≅ V)
    (g : V ⟶ T) (f' : W ⟶ V') (e' : U' ≅ V') (g' : V' ⟶ T) (k : T ⟶ S)
    (h : f ≫ g = f' ≫ g') :
    (f ≫ e.inv) ≫ e.hom ≫ g ≫ k = (f' ≫ e'.inv) ≫ e'.hom ≫ g' ≫ k := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h, Category.assoc]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- The cancellation closing `map_comp_edge_app`: one inverse-forward pair cancels and the
remaining square is `h`. Stated over variable objects for the same reason as
`comp_comp_inv_hom_comp`. -/
private theorem comp_comp_eq_comp_inv_hom {W V V' U T S : 𝒜} (a : W ⟶ V) (b : V ⟶ T)
    (f : W ⟶ V') (e : U ≅ V') (g : V' ⟶ T) (k : T ⟶ S) (h : a ≫ b = f ≫ g) :
    a ≫ b ≫ k = (f ≫ e.inv) ≫ e.hom ≫ g ≫ k := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h, Category.assoc]

omit [Abelian 𝒜] [HasInjectiveResolutions 𝒜] in
/-- Removing an identity from the middle of a composite, for an endomorphism `m` known to be the
identity. Stated over variable objects for the same reason as `comp_comp_inv_hom_comp`. -/
private theorem comp_comp_eq_comp_of_eq_id {W V U : 𝒜} (a : W ⟶ V) (m : V ⟶ V) (c : V ⟶ U)
    (hm : m = 𝟙 V) : a ≫ m ≫ c = a ≫ c := by
  rw [hm, Category.id_comp]

/-! ### The edge morphism of a composite -/

section Comp

variable (P₂ : 𝒞 ⥤ ℬ) [P₂.Additive] [P₂.PreservesInjectiveObjects]
  (P₁ : ℬ ⥤ 𝒜) [P₁.Additive] [P₁.PreservesInjectiveObjects]
  (Q : 𝒜 ⥤ ℰ) [Q.Additive]

/-- **The edge morphism of a composite is the composite of the edge morphisms.** For
`P₂ : 𝒞 ⥤ ℬ` and `P₁ : ℬ ⥤ 𝒜` both preserving injective objects, the edge morphism of
`(P₂ ⋙ P₁, Q)` at `W` factors as the edge morphism of `(P₁, Q)` at `P₂ W` followed by the edge
morphism of `(P₂, P₁ ⋙ Q)` at `W`.

In the geometric reading this is the statement that the pullback map on cohomology along a
composite `X ⟶ Y ⟶ Z` of morphisms is the composite of the two pullback maps. -/
theorem edge_app_comp (n : ℕ) (W : 𝒞) :
    (edge (P₂ ⋙ P₁) Q n).app W =
      (edge P₁ Q n).app (P₂.obj W) ≫ (edge P₂ (P₁ ⋙ Q) n).app W := by
  have ha₂ := ι_f_zero_comp_resolutionComparison P₂ W
  have ha₁ := ι_f_zero_comp_resolutionComparison P₁ (P₂.obj W)
  have ha : (injectiveResolution (P₁.obj (P₂.obj W))).ι.f 0 ≫
      ((resolutionComparison P₁ (P₂.obj W)) ≫
        (P₁.mapHomologicalComplex (ComplexShape.up ℕ)).map (resolutionComparison P₂ W)).f 0 =
      (P₂ ⋙ P₁).map ((injectiveResolution W).ι.f 0) :=
    comp_comp_eq _ ((resolutionComparison P₁ (P₂.obj W)).f 0)
      (P₁.map ((resolutionComparison P₂ W).f 0)) _ _ ha₁
      (map_comp_eq_map P₁ _ _ _ ha₂)
  rw [edge_app_eq (P₂ ⋙ P₁) Q n (injectiveResolution W)
      (injectiveResolution (P₁.obj (P₂.obj W))) _ ha,
    edge_app_eq P₁ Q n (injectiveResolution (P₂.obj W))
      (injectiveResolution (P₁.obj (P₂.obj W))) _ ha₁,
    edge_app_eq P₂ (P₁ ⋙ Q) n (injectiveResolution W) (injectiveResolution (P₂.obj W)) _ ha₂,
    Functor.map_comp, HomologicalComplex.homologyMap_comp,
    mapHomologicalComplex_map_mapHomologicalComplex_map]
  simp only [Category.assoc]
  exact comp_comp_inv_hom_comp _ _ _ _ _

end Comp

/-! ### Compatibility with a natural transformation of the target -/

section Target

variable (P : ℬ ⥤ 𝒜) [P.Additive] [P.PreservesInjectiveObjects]
  {Q Q' : 𝒜 ⥤ ℰ} [Q.Additive] [Q'.Additive]

end Target

/-! ### Compatibility with a natural transformation of the source -/

section Source

variable {P P' : ℬ ⥤ 𝒜} [P.Additive] [P.PreservesInjectiveObjects]
  [P'.Additive] [P'.PreservesInjectiveObjects]
  (Q : 𝒜 ⥤ ℰ) [Q.Additive]

/-- **The edge morphism is compatible with a natural transformation of the source functor.** For
`ρ : P ⟶ P'`, the map induced by `ρ` on `Qⁿ` followed by the edge morphism of `(P', Q)` is the
edge morphism of `(P, Q)` followed by the map induced on right derived functors by `ρ` whiskered
with `Q`.

This is the law a base-change square of sites consumes: there `P` and `P'` are the two composites
of direct images around the square and `ρ` is the comparison between them, so this says the
pullback map on cohomology may be computed along either side of the square. -/
theorem map_comp_edge_app (ρ : P ⟶ P') (n : ℕ) (X : ℬ) :
    (Q.rightDerived n).map (ρ.app X) ≫ (edge P' Q n).app X =
      (edge P Q n).app X ≫
        (NatTrans.rightDerived (Functor.whiskerRight ρ Q) n).app X := by
  have ha := ι_f_zero_comp_resolutionComparison P X
  have ha' := ι_f_zero_comp_resolutionComparison P' X
  have hcc : (injectiveResolution (P.obj X)).ι.f 0 ≫
      (InjectiveResolution.desc (ρ.app X) (injectiveResolution (P'.obj X))
        (injectiveResolution (P.obj X))).f 0 =
      ρ.app X ≫ (injectiveResolution (P'.obj X)).ι.f 0 :=
    InjectiveResolution.desc_commutes_zero _ _ _
  have hinj : ∀ m, Injective
      ((((P'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex)).X m) :=
    injective_mapHomologicalComplex_obj P' _ (injectiveResolution X).injective
  have key : HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (ρ.app X) (injectiveResolution (P'.obj X))
            (injectiveResolution (P.obj X)) ≫ resolutionComparison P' X)) n =
      HomologicalComplex.homologyMap
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (resolutionComparison P X ≫ (NatTrans.mapHomologicalComplex ρ
            (ComplexShape.up ℕ)).app (injectiveResolution X).cocomplex)) n := by
    refine homologyMap_map_eq_of_aug Q (injectiveResolution (P.obj X)) hinj _ _ ?_ n
    have hl : (injectiveResolution (P.obj X)).ι.f 0 ≫
        (InjectiveResolution.desc (ρ.app X) (injectiveResolution (P'.obj X))
            (injectiveResolution (P.obj X)) ≫ resolutionComparison P' X).f 0 =
          ρ.app X ≫ P'.map ((injectiveResolution X).ι.f 0) :=
      comp_comp_eq_assoc _ _ ((resolutionComparison P' X).f 0) (ρ.app X)
        ((injectiveResolution (P'.obj X)).ι.f 0) _ hcc ha'
    have hr : (injectiveResolution (P.obj X)).ι.f 0 ≫
        (resolutionComparison P X ≫ (NatTrans.mapHomologicalComplex ρ
            (ComplexShape.up ℕ)).app (injectiveResolution X).cocomplex).f 0 =
          ρ.app X ≫ P'.map ((injectiveResolution X).ι.f 0) :=
      comp_comp_eq_of_eq _ ((resolutionComparison P X).f 0)
        (ρ.app ((injectiveResolution X).cocomplex.X 0))
        (P.map ((injectiveResolution X).ι.f 0)) (ρ.app X) _ ha
        (ρ.naturality ((injectiveResolution X).ι.f 0))
    rw [hl, hr]
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp, Functor.map_comp,
    HomologicalComplex.homologyMap_comp] at key
  rw [edge_app_eq P Q n (injectiveResolution X) (injectiveResolution (P.obj X)) _ ha,
    edge_app_eq P' Q n (injectiveResolution X) (injectiveResolution (P'.obj X)) _ ha',
    InjectiveResolution.rightDerived_app_eq (Functor.whiskerRight ρ Q)
      (injectiveResolution X) n,
    InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc (ρ.app X)
      (injectiveResolution (P.obj X)) (injectiveResolution (P'.obj X)) _ hcc Q n]
  simp only [Category.assoc, HomologicalComplex.homologyFunctor_map]
  refine (cancel_epi ((injectiveResolution (P.obj X)).isoRightDerivedObj Q n).hom).mpr ?_
  exact comp_comp_eq_comp_inv_hom _ _ _ _ _ _ key

end Source

/-! ### The edge morphism of an exact functor -/

section Exact

variable (P : ℬ ⥤ 𝒜) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [P.PreservesInjectiveObjects] (Q : 𝒜 ⥤ ℰ) [Q.Additive]

/-- **The edge morphism of an exact functor preserving injectives is an isomorphism.** An exact
functor preserving injective objects carries an injective resolution to an injective resolution
(`Stacks.Cohomology.CompositeRightDerived.mapInjRes`), so the comparison of resolutions computing
the edge morphism may be taken to be the identity.

This is Stacks 015Z read on one object; the global statement is
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`. -/
instance isIso_edge_app (n : ℕ) (X : ℬ) : IsIso ((edge P Q n).app X) := by
  have h0 : (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).ι.f 0 =
      P.map ((injectiveResolution X).ι.f 0) := by
    dsimp [Stacks.Cohomology.CompositeRightDerived.mapInjRes]; simp
  have ha : (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).ι.f 0 ≫
      HomologicalComplex.Hom.f (𝟙 (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).cocomplex) 0 =
      P.map ((injectiveResolution X).ι.f 0) := by
    rw [HomologicalComplex.id_f, Category.comp_id, h0]
  have heq : (edge P Q n).app X =
      ((Stacks.Cohomology.CompositeRightDerived.mapInjRes P
          (injectiveResolution X)).isoRightDerivedObj Q n).hom ≫
        ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).inv := by
    rw [edge_app_eq P Q n (injectiveResolution X)
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes P (injectiveResolution X))
      (𝟙 (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).cocomplex) ha]
    have hid : HomologicalComplex.homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (𝟙 (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
          (injectiveResolution X)).cocomplex)) n = 𝟙 _ := by
      rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
    exact comp_comp_eq_comp_of_eq_id _ _ _ hid
  rw [heq]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_inv _)

end Exact

end Stacks.Cohomology.RightDerivedEdge

end
