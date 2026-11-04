module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionLevelFormula

/-!
# The composition law for the map on cohomology along a morphism of ringed spaces

The arrow `RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)` of [Stacks, Tag 01F9] that an `f`-map induces, and the map
`H^i(Y, 𝒢) ⟶ H^i(X, ℱ)` of [Stacks, Tag 01FA] obtained from it, are built from the morphism
`𝒢[0] ⟶ Rf_*(ℱ[0])` of [Stacks, Tag 01F8], which is
`Stacks.Cohomology.singleRightDerivedUnit` composed with `φ[0]`. Both are functorial in the two
*module* arguments; the law in the *morphism* argument needs
`Stacks.Cohomology.singleRightDerivedUnit` to be **multiplicative**, and that is what this file
proves.

## Main results

* `Stacks.Cohomology.singleRightDerivedUnit_comp_rightDerivedFunctorPlusComp_app`:
  **`singleRightDerivedUnit` is multiplicative modulo the comparison of [Stacks, Tag 05T2]**.
  For additive functors `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` and an object `M` of `𝒜`,
  ```
  (singleRightDerivedUnit (F ⋙ G)).app M ≫ t = (singleRightDerivedUnit G).app (F M) ≫
    RG((singleRightDerivedUnit F).app M)
  ```
  where `t = CategoryTheory.Functor.rightDerivedFunctorPlusComp F G` is the canonical
  transformation `R(G ∘ F) ⟶ RF ⋙ RG` read at `M[0]`. No acyclicity and no preservation of
  injectives is needed: `t` exists for any additive pair.
* `Stacks.Cohomology.singleRightDerivedUnit_comp_natIsoOfIso_comp_app`: the same law read
  through a transport of `R(G ∘ F)` along an isomorphism of `G ∘ F` with itself whose degreewise
  image has identity components. This is the shape in which the comparison of
  [Stacks, Tag 01F5] presents itself.

The two steps it is assembled from, each the multiplicativity of a comparison that places a
functor's image of `M[0]` against `(F M)[0]`:

* `HomologicalComplex.singleMapHomologicalComplex_hom_app_comp`: degreewise, for cochain
  complexes.
* `Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom_comp`: in the bounded below
  homotopy category.

## Implementation notes

The chase is short because of two facts already in the development. First,
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac_app` pins the canonical comparison `t`
by its composite with the unit of `R(G ∘ F)`, and the coherence isomorphism appearing there,
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))`, has identity
components — `Stacks.Cohomology.BaseChange.mapHomotopyCategoryPlusCompIso_refl_inv_comp`.
Second, `Stacks.Cohomology.ModulePushforwardComparison.mapSingleFunctorCompQhIso_hom_app_comp`
gives a closed form for the coherence isomorphism inside
`Stacks.Cohomology.singleRightDerivedUnit`: it comes from the bounded below homotopy category,
as `DerivedCategory.Plus.Qh` of
`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom`. So after both units are
unfolded the identity is the naturality of the unit of `RG` along `singleMapPlusHom F M`,
together with the multiplicativity of `singleMapPlusHom` itself; and that last statement lives
in the homotopy category, where it is `HomologicalComplex.singleMapHomologicalComplex`
multiplicativity, checked degreewise.

Every step of the chase that is pure reassociation is a `private` lemma stated on *variables*,
not written inline: the two sides meet at objects that have two definitionally equal spellings
(`R(G ∘ F)` read at `Qh(ℱ[0])` against `RG(RF(Qh ℱ[0]))`, and `(G ∘ F)(ℱ[0])` against
`G(F(ℱ[0]))`), and a `rw` through such a junction builds a motive that is not type-correct
under the `implicit` transparency level. `comp_eq_of_naturality_of_fac` has the same shape as
the lemma of that name in
`StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit`, which runs the
analogous chase for `mapCochainComplexPlusDerivedUnit`; that one is `private`, so it cannot be
cited from here.

**What this does not reach.** `Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso`,
the Leray comparison of [Stacks, Tag 01F5], is `t` precomposed with the transport
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso` along
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g`.
`singleRightDerivedUnit_comp_natIsoOfIso_comp_app` is the law read through such a transport,
and the one hypothesis it asks for is that the degreewise image of the underived comparison has
identity components. That hypothesis is *about the pushforward of sheaves of modules*, not
about homological algebra, and it is not discharged here — this file knows nothing of ringed
spaces.

Nothing here carries a Stacks tag: [Stacks, Tag 01FA] states only the displayed map, so the
functoriality laws of that map are not clauses of a tag.

## References

* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Degreewise: the comparison of `M[0]` with `(F M)[0]` is multiplicative -/

namespace HomologicalComplex

/-- **`HomologicalComplex.singleMapHomologicalComplex` is multiplicative.** Comparing
`G(F(M[0]))` with `(G(F M))[0]` in one step is the same as comparing `F(M[0])` with `(F M)[0]`,
applying `G` degreewise, and then comparing `G((F M)[0])` with `(G(F M))[0]`.

In degree `j` all three comparisons are built from `HomologicalComplex.singleObjXSelf`, and the
two copies of it at `F M` cancel; in every other degree the source is a zero object. -/
theorem singleMapHomologicalComplex_hom_app_comp {W₁ : Type u₁} {W₂ : Type u₂} {W₃ : Type u₃}
    [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{v₃} W₃]
    [Preadditive W₁] [Preadditive W₂] [Preadditive W₃]
    [HasZeroObject W₁] [HasZeroObject W₂] [HasZeroObject W₃]
    {ι : Type*} (c : ComplexShape ι) [DecidableEq ι]
    (F : W₁ ⥤ W₂) (G : W₂ ⥤ W₃) [F.Additive] [G.Additive] (j : ι) (M : W₁) :
    (G.mapHomologicalComplex c).map ((singleMapHomologicalComplex F c j).hom.app M) ≫
        (singleMapHomologicalComplex G c j).hom.app (F.obj M) =
      (singleMapHomologicalComplex (F ⋙ G) c j).hom.app M := by
  ext i
  by_cases h : i = j
  · subst h
    simp
  · simp [singleMapHomologicalComplex_hom_app_ne _ _ h]

end HomologicalComplex

/-! ### In the bounded below homotopy category -/

namespace Stacks.Cohomology.ModulePushforwardComparison

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive] [G.Additive]

/-- **`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is multiplicative.** In the
ambient homotopy category the comparison of `G(F(M[0]))` with `(G(F M))[0]` factors through
`G((F M)[0])`. By
`Stacks.Cohomology.ModulePushforwardComparison.mapHomotopyCategorySingleFunctor_hom_app` each
factor is the class of `HomologicalComplex.singleMapHomologicalComplex`, where the statement is
`HomologicalComplex.singleMapHomologicalComplex_hom_app_comp`. -/
theorem mapHomotopyCategorySingleFunctor_hom_app_comp (M : C₁) :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((F.mapHomotopyCategorySingleFunctor 0).hom.app M) ≫
        (G.mapHomotopyCategorySingleFunctor 0).hom.app (F.obj M) =
      ((F ⋙ G).mapHomotopyCategorySingleFunctor 0).hom.app M := by
  have h1 : (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategorySingleFunctor 0).hom.app M) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app
            M)) :=
    congrArg (fun t => (G.mapHomotopyCategory (ComplexShape.up ℤ)).map t)
      (mapHomotopyCategorySingleFunctor_hom_app F M)
  have key : (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app
              M)) ≫
        (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
            (F.obj M)) =
      (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (ComplexShape.up ℤ) 0).hom.app
          M) :=
    ((HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (fun t => (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map t)
        (HomologicalComplex.singleMapHomologicalComplex_hom_app_comp (ComplexShape.up ℤ) F G 0 M))
  rw [h1, mapHomotopyCategorySingleFunctor_hom_app G (F.obj M),
    mapHomotopyCategorySingleFunctor_hom_app (F ⋙ G) M]
  exact key

/-- **`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom` is multiplicative.** In
`K⁺(𝒞)` the comparison of `G(F(M[0]))` with `(G(F M))[0]` factors through `G((F M)[0])`.

The bounded below homotopy category is a full subcategory of the homotopy category, so it is
enough to compare the two sides there, where
`Stacks.Cohomology.ModulePushforwardComparison.ι_map_singleMapPlusHom` identifies each factor
and `mapHomotopyCategorySingleFunctor_hom_app_comp` is the statement. The last of those three
identifications is applied by a term rather than by `rw`: the two sides of the goal are then
typed through different spellings of the composite functor on complexes, and the rewrite motive
is not type-correct under the `implicit` transparency level. -/
theorem singleMapPlusHom_comp (M : C₁) :
    G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M) ≫ singleMapPlusHom G (F.obj M) =
      singleMapPlusHom (F ⋙ G) M := by
  apply (HomotopyCategory.Plus.ι C₃).map_injective
  have hι : (HomotopyCategory.Plus.ι C₃).map
        (G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M)) =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.Plus.ι C₂).map (singleMapPlusHom F M)) := rfl
  rw [Functor.map_comp, hι, ι_map_singleMapPlusHom, ι_map_singleMapPlusHom]
  exact (mapHomotopyCategorySingleFunctor_hom_app_comp F G M).trans
    (ι_map_singleMapPlusHom (F ⋙ G) M).symm

end Stacks.Cohomology.ModulePushforwardComparison

/-! ### The multiplicativity of `singleRightDerivedUnit` -/

namespace Stacks.Cohomology

open ModulePushforwardComparison

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The reassociation that turns the naturality of the comparison `t` and the factorization
pinning it into a single rewriting of a four-fold composite. Stated on variables so that it can
be instantiated at the two definitionally equal spellings of the junction object — `R(G ∘ F)`
read at `Qh(K)` against `RG(RF(Qh K))` — without any transport. -/
private lemma comp_eq_of_naturality_of_fac {D : Type*} [Category* D]
    {X₀ X₁ X₂ X₃ X₄ Y Z : D} (i : X₀ ⟶ X₁) (u : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (c : X₃ ⟶ X₄)
    (c' : X₂ ⟶ Y) (n : Y ⟶ X₄) (r : X₁ ⟶ Z) (s : Z ⟶ Y)
    (hnat : m ≫ c = c' ≫ n) (hfac : u ≫ c' = r ≫ s) :
    (i ≫ u ≫ m) ≫ c = i ≫ r ≫ s ≫ n := by
  simp [hnat, reassoc_of% hfac]

/-- The cancellation of a split pair underneath a functor, stated on variables for the same
reason: the comparison `Qh(G(sMPH))` is inverted by the two coherence isomorphisms of
`Stacks.Cohomology.singleRightDerivedUnit`, and the objects at which it is read have two
spellings. -/
private lemma eq_comp_of_naturality_of_comp_eq_id {D E : Type*} [Category* D] [Category* E]
    (R : E ⥤ D) {X₀ X₁ X₂ : D} {Y₀ Y₁ : E}
    (i : X₀ ⟶ X₁) (x : X₁ ⟶ X₂) (u₀ : X₁ ⟶ R.obj Y₀) (u₁ : X₂ ⟶ R.obj Y₁)
    (x' : Y₀ ⟶ Y₁) (w : Y₁ ⟶ Y₀)
    (hnat : x ≫ u₁ = u₀ ≫ R.map x') (hone : x' ≫ w = 𝟙 Y₀) :
    (i ≫ x) ≫ u₁ ≫ R.map w = i ≫ u₀ := by
  have h : R.map x' ≫ R.map w = 𝟙 _ := by rw [← R.map_comp, hone, R.map_id]
  simp [reassoc_of% hnat, h]

/-- An isomorphism can be cancelled on the right. Stated on variables for the same reason: the
object `(G ∘ F)(M)` has the two spellings `(F ⋙ G).obj M` and `G.obj (F.obj M)`, and the
identifications being composed are indexed at different ones. -/
private lemma eq_of_comp_iso_hom_eq {D : Type*} [Category* D] {X Y Z : D} (e : Y ≅ Z)
    {u v : X ⟶ Y} (h : u ≫ e.hom = v ≫ e.hom) : u = v :=
  (cancel_mono e.hom).mp h

/-- Two isomorphisms with a common target are exchanged by a morphism of their sources exactly
when their inverses are. Stated on variables for the same reason: the source of the morphism
`Qh(G(sMPH))` has the spelling `Qh(G_*(F_*(M[0])))`, and the target of the coherence isomorphism
for `G ∘ F` the spelling `Qh((G ∘ F)_*(M[0]))`. -/
private lemma inv_comp_eq_inv {D : Type*} [Category* D] {X₀ X₁ X₂ : D}
    (α : X₁ ≅ X₀) (β : X₂ ≅ X₀) (x : X₁ ⟶ X₂) (h : x ≫ β.hom = α.hom) :
    α.inv ≫ x = β.inv := by
  rw [Iso.inv_comp_eq, ← h]
  simp

/-- The regrouping of the right hand side, stated on variables for the same reason: the two
sides split the image under `RG` of the coherence isomorphism at a different place. -/
private lemma comp_eq_of_star {D E : Type*} [Category* D] [Category* E] (R : E ⥤ D)
    {X₀ X₁ X₂ : D} {Y₀ Y₁ Y₂ Y₃ Y₄ : E}
    (i : X₀ ⟶ X₁) (r : X₁ ⟶ R.obj Y₂) (a : X₀ ⟶ X₂) (b : X₂ ⟶ R.obj Y₀)
    (p₁ : Y₀ ⟶ Y₁) (p₂ : Y₁ ⟶ Y₂) (u : Y₂ ⟶ Y₃) (m : Y₃ ⟶ Y₄)
    (hstar : i ≫ r = a ≫ b ≫ R.map (p₁ ≫ p₂)) :
    i ≫ r ≫ R.map u ≫ R.map m = (a ≫ b ≫ R.map p₁) ≫ R.map (p₂ ≫ u ≫ m) := by
  rw [← Category.assoc i r, hstar]
  simp only [Category.assoc, ← Functor.map_comp]

section Multiplicative

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [EnoughInjectives A] [EnoughInjectives B]

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B] in
/-- **`CategoryTheory.Functor.mapSingleFunctorCompQhIso` is multiplicative.** The comparison
identifying `Qh(G(F(M[0])))` with `(G(F M))[0]` is the image under `Qh` of the comparison in the
homotopy category for `F`, followed by the comparison for `G`.

Both sides become `Qh` of
`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom` after composing with the
identification `(G(F M))[0] ≅ Qh((G(F M))[0])` of
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh`, by
`Stacks.Cohomology.ModulePushforwardComparison.mapSingleFunctorCompQhIso_hom_app_comp`, and
there the statement is
`Stacks.Cohomology.ModulePushforwardComparison.singleMapPlusHom_comp`. -/
theorem mapSingleFunctorCompQhIso_hom_app_comp_hom_app (M : A) :
    DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M)) ≫
        (Functor.mapSingleFunctorCompQhIso G).hom.app (F.obj M) =
      (Functor.mapSingleFunctorCompQhIso (F ⋙ G)).hom.app M :=
  eq_of_comp_iso_hom_eq
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app (G.obj (F.obj M)))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => DerivedCategory.Plus.Qh.map
            (G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M)) ≫ z)
          (mapSingleFunctorCompQhIso_hom_app_comp G (F.obj M))).trans
        ((DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
          ((congrArg (fun z => DerivedCategory.Plus.Qh.map z)
              (singleMapPlusHom_comp F G M)).trans
            (mapSingleFunctorCompQhIso_hom_app_comp (F ⋙ G) M).symm))))

/-- **`Stacks.Cohomology.singleRightDerivedUnit` is multiplicative, modulo the comparison of
[Stacks, Tag 05T2].** For additive functors `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` with `𝒜` and `ℬ` having
enough injectives, and `t : R(G ∘ F) ⟶ RF ⋙ RG` the canonical comparison
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`,

```
(G(F M))[0] ⟶ R(G ∘ F)(M[0]) ⟶ RG(RF(M[0]))
```

is the same as

```
(G(F M))[0] ⟶ RG((F M)[0]) ⟶ RG(RF(M[0])).
```

This is the law the composition rule in the *morphism* for the arrow of [Stacks, Tag 01F9] and
the map of [Stacks, Tag 01FA] rests on: for morphisms of ringed spaces `f : X ⟶ Y` and
`g : Y ⟶ Z` the two functors are `f_*` and `g_*`, and `t` inverted is the comparison of
[Stacks, Tag 01F5].

No acyclicity and no preservation of injective objects is assumed: `t` is defined for every
additive pair, and only the factorization pinning it is used. -/
theorem singleRightDerivedUnit_comp_rightDerivedFunctorPlusComp_app (M : A) :
    (singleRightDerivedUnit (F ⋙ G)).app M ≫
        (Functor.rightDerivedFunctorPlusComp F G).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (singleRightDerivedUnit G).app (F.obj M) ≫
        G.rightDerivedFunctorPlus.map ((singleRightDerivedUnit F).app M) := by
  have hid : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    rfl
  have hone : DerivedCategory.Plus.Qh.map
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) = 𝟙 _ := by
    rw [hid]
    exact DerivedCategory.Plus.Qh.map_id _
  have hfac0 := Functor.rightDerivedFunctorPlusComp_fac_app F G
    ((HomotopyCategory.Plus.singleFunctor A 0).obj M)
  rw [hone] at hfac0
  have hfac : (F ⋙ G).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ≫
      (Functor.rightDerivedFunctorPlusComp F G).app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) =
      G.rightDerivedFunctorPlusUnit.app
          (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) :=
    hfac0.trans (Category.id_comp _)
  have hsmpf : DerivedCategory.Plus.Qh.map (singleMapPlusHom F M) ≫
      ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj M) ≫
        ((Functor.mapSingleFunctorCompQhIso F).app M).inv) = 𝟙 _ := by
    rw [← mapSingleFunctorCompQhIso_hom_app_comp F M]
    simp
  have hinv := inv_comp_eq_inv ((Functor.mapSingleFunctorCompQhIso (F ⋙ G)).app M)
    ((Functor.mapSingleFunctorCompQhIso G).app (F.obj M))
    (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M)))
    (mapSingleFunctorCompQhIso_hom_app_comp_hom_app F G M)
  have hstar := eq_comp_of_naturality_of_comp_eq_id G.rightDerivedFunctorPlus
    ((Functor.mapSingleFunctorCompQhIso (F ⋙ G)).app M).inv
    (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map (singleMapPlusHom F M)))
    (G.rightDerivedFunctorPlusUnit.app
      (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))
    (G.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj M)))
    (DerivedCategory.Plus.Qh.map (singleMapPlusHom F M))
    ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj M) ≫
      ((Functor.mapSingleFunctorCompQhIso F).app M).inv)
    (G.rightDerivedFunctorPlusUnit.naturality (singleMapPlusHom F M)) hsmpf
  rw [hinv] at hstar
  rw [singleRightDerivedUnit_app, singleRightDerivedUnit_app, singleRightDerivedUnit_app]
  refine (comp_eq_of_naturality_of_fac
    ((Functor.mapSingleFunctorCompQhIso (F ⋙ G)).app M).inv
    ((F ⋙ G).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M))
    ((F ⋙ G).rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M))
    ((Functor.rightDerivedFunctorPlusComp F G).app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M))
    ((Functor.rightDerivedFunctorPlusComp F G).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))
    (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)))
    (G.rightDerivedFunctorPlusUnit.app
      (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))
    (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))
    ((Functor.rightDerivedFunctorPlusComp F G).naturality
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) hfac).trans ?_
  exact comp_eq_of_star G.rightDerivedFunctorPlus
    ((Functor.mapSingleFunctorCompQhIso (F ⋙ G)).app M).inv
    (G.rightDerivedFunctorPlusUnit.app
      (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj M)))
    ((Functor.mapSingleFunctorCompQhIso G).app (F.obj M)).inv
    (G.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj M)))
    ((Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj M))
    ((Functor.mapSingleFunctorCompQhIso F).app M).inv
    (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj M))
    (F.rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M))
    hstar.symm

/-- **The multiplicativity of [Stacks, Tag 01F8] through a transport of the composite.** The
comparison of [Stacks, Tag 01F5] is not the canonical `t` of [Stacks, Tag 05T2] outright: it is
`t` precomposed with
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso` along the
underived comparison `(g ∘ f)_* ≅ g_* ∘ f_*` of [Stacks, Tag 0097] (1). For a morphism of
ringed spaces that comparison has *equal* ends
(`Stacks.PullbackPseudofunctor.modulePushforward_comp` holds by `rfl`) and identity degreewise
image, so the transport is the identity
(`...rightDerivedFunctorPlusNatIsoOfIso_hom_eq_id`) and
`singleRightDerivedUnit_comp_rightDerivedFunctorPlusComp_app` applies through it. -/
theorem singleRightDerivedUnit_comp_natIsoOfIso_comp_app (e : F ⋙ G ≅ F ⋙ G)
    (he : ∀ K : HomotopyCategory.Plus A,
      (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj = 𝟙 _)
    (M : A) :
    (singleRightDerivedUnit (F ⋙ G)).app M ≫
        (HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso e).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
        (Functor.rightDerivedFunctorPlusComp F G).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (singleRightDerivedUnit G).app (F.obj M) ≫
        G.rightDerivedFunctorPlus.map ((singleRightDerivedUnit F).app M) := by
  have happ : (HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso e).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj M) = 𝟙 _ := by
    rw [HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso_hom_eq_id e he]
    rfl
  rw [happ]
  exact (congrArg (fun z => (singleRightDerivedUnit (F ⋙ G)).app M ≫ z)
      (Category.id_comp ((Functor.rightDerivedFunctorPlusComp F G).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M)))).trans
    (singleRightDerivedUnit_comp_rightDerivedFunctorPlusComp_app F G M)

end Multiplicative

end Stacks.Cohomology

end
