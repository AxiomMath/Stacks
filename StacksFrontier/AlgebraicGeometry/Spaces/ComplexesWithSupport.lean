module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian

/-!
# Complexes of abelian sheaves supported on a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. This file
constructs the derived category `D(X_étale)` of abelian sheaves on the small étale site of `X`
and its full subcategory `D_{|Z|}(X_étale)` of complexes all of whose cohomology sheaves are
supported on the point set of `Z`, and proves the sheaf-level input to the identification of
that subcategory with `D(Z_étale)`: the small étale direct image along `i` of an abelian sheaf
on `Z` is supported on `|Z|`.

## Main definitions

* `AlgebraicGeometry.Space.abelianSheaves` is the category of abelian sheaves on the small
  étale site of an algebraic space, and `AlgebraicGeometry.Space.smallEtaleDerivedCategory` is
  its derived category `D(Y_étale)`.
* `AlgebraicGeometry.Space.cohomologySupportedOn` is the property of an object of that derived
  category that all its cohomology sheaves are supported on a given subset of the point set,
  `AlgebraicGeometry.Space.smallEtaleDerivedCategoryWithSupport` is the full subcategory it cuts
  out, and `AlgebraicGeometry.Space.smallEtaleDerivedCategoryOnClosedSubspace` is the case
  `D_{|Z|}(X_étale)` of the point set of a closed immersion `i : Z ⟶ X`.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward` is the small étale direct image of
  abelian sheaves along a representable morphism, and
  `AlgebraicGeometry.Space.chartPreimage` is the preimage of the point set of a morphism in the
  point set of an étale chart.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.bot_mem_topology`,
  `AlgebraicGeometry.Space.eq_zero_of_isEmpty_chart` and
  `AlgebraicGeometry.Space.isEmpty_smallBaseChange_of_disjoint_range`: the empty sieve covers an
  étale chart with no points, so an abelian sheaf has only the zero section there, and a chart
  of `X` whose points avoid `|Z|` has empty base change along a closed immersion `i : Z ⟶ X`.
* `AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset`: **the support of
  a direct image.** For a closed immersion `i : Z ⟶ X` the support of `i_*G` is contained in
  `|Z|`, for every abelian sheaf `G` on `Z_étale` and in every coefficient universe. This is
  Étale Cohomology 04FX for algebraic spaces, and
  `AlgebraicGeometry.Space.isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem` is its
  stalkwise form.
* `AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range`: a geometric point of `X`
  whose image lies in `|Z|` is the image of a geometric point of `Z`, over the same field.
* `AlgebraicGeometry.Space.forgetStalkFunctorIso` and
  `AlgebraicGeometry.Space.isZero_stalkFunctor_iff_subsingleton_stalkSet`: forgetting the group
  structure commutes with the abelian geometric stalk, so the vanishing of that stalk is the
  triviality of the set-valued stalk through which the support is defined.
* `AlgebraicGeometry.Space.isIso_of_isIso_stalkFunctor_map`: the abelian geometric stalks are
  conservative on abelian sheaves on the small étale site.
* `AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset`: **Étale Cohomology 04CA,
  part (2), for algebraic spaces.** The unit `F ⟶ i_*i^{-1}F` is invertible at every abelian
  sheaf supported on `|Z|`;
  `AlgebraicGeometry.Space.unitIsoOnSupportedSheaves_of_isClosedImmersion` is the sectionwise form
  `AlgebraicGeometry.Space.UnitIsoOnSupportedSheaves` of that statement.
* `AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion`:
  **Stacks 04E5, part (2), the essential image**, in both directions and unconditionally.
* `AlgebraicGeometry.Space.pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion` is the
  adjunction `i_* ⊣ H_Z` of Stacks 0A4M with that clause discharged, and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isClosedImmersion` is the
  exactness of `i_*` which follows from it, Stacks 0A4K for a closed immersion without the
  surjectivity hypothesis under which it is otherwise carried.
* `AlgebraicGeometry.Space.eq_zero_of_supportOfSheaf_eq_empty`,
  `AlgebraicGeometry.Space.supportOfSheaf_eq_empty_of_subset_range` and
  `AlgebraicGeometry.Space.eq_zero_of_subset_range_of_stalk`: an abelian sheaf supported on
  `|Z|` whose stalk at the image of every geometric point of `Z` is trivial is zero.

## Implementation notes

The support lemmas are at a free coefficient universe `w`: the direct image is restriction along
the chart base-change functor of Stacks 03G2, part (4), so by itself it needs no sheafification
and no universe restriction at all. Everything mentioning the inverse image is at `u + 1`, the
universe in which the objects of the small étale site live; there the site carries `HasSheafify`
for abelian groups as an instance, so the inverse image is the honest functor
`CategoryTheory.Functor.sheafPullback` and not a left adjoint extracted from an existence
statement, and that is also the universe of the left-inverse clause of Stacks 04E5, part (2) and
of the stalk computation of Stacks 04K2, part (4) for abelian sheaves.
`AlgebraicGeometry.Space.smallEtale_hasSheafify_addCommGrpCat` records sheafification at the
wider universe `max (u + 1) v` as a theorem rather than an instance, as
`AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian` does, so that it cannot
hide the general instances at the coefficient universe `u`.

The support of a direct image is computed through the *sections* description of the support of a
sheaf, Stacks 04KB, rather than through stalks. For a chart `V` of `X` and a section `σ` of
`i_*G` over `V`, the preimage of `|Z|` in the point set of `V` is closed, and every chart of `X`
over `V` whose points avoid that preimage has empty base change along `i`, hence carries only
the zero section of `i_*G`. So the complement of the preimage is contained in the largest open
zero locus of `σ` by maximality, which bounds the support of `σ` by the preimage of `|Z|`. No
geometric point is chosen, and no comparison of étale local rings at two geometric points over
one point of `|X|` -- the content of Stacks 04K0, which this tree does not carry -- is needed.

The essential-image clause is then proved stalkwise, as the source proves it for schemes. At a
geometric point of `X` lying over `|Z|` the point comes from a geometric point of `Z`, where the
inverse image already carries the unit to an isomorphism by the triangle identity and the
left-inverse clause of Stacks 04E5, part (2); at a geometric point whose image misses `|Z|` both
stalks vanish. Conservativity of the abelian stalks is obtained from parts (1) and (2) of
Stacks 04K5 for sheaves of sets, through the identification of the forgetful image of the
abelian stalk with the set-valued stalk, both being the fibre at the point of the site
determined by the geometric point.

The equivalence `D(Z_étale) ≌ D_{|Z|}(X_étale)` of Stacks 0AEI is **not** proved and no
declaration carries `@[stacks 0AEI]`. With the exactness of `i_*` above, the direct image does
induce a functor `CategoryTheory.Functor.mapDerivedCategory` on derived categories; what is
missing is generic: Mathlib records no compatibility of that construction with composition of
functors, with isomorphisms of functors, with the identity, or with adjunctions, and no
commutation with the homology functors, so the full faithfulness of the induced functor and the
identification of its essential image cannot be assembled here.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étale charts with no points -/

/-- The empty sieve is a covering sieve of an étale chart whose underlying scheme has no
points: the empty family is an fppf covering family of such a scheme, it is étale because it
is empty, and it satisfies every cardinality bound. -/
theorem SmallEtale.bot_mem_topology (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (E : SmallEtale B S hS F)
    (hE : IsEmpty ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj E))) :
    (⊥ : Sieve E) ∈ SmallEtale.topology B S hS F E := by
  have hE' : IsEmpty (B.inclusion.obj ((SmallEtale.toSchemes B S hS F).obj E)) := hE
  have hbotPre : (⊥ : Presieve E) ∈ SmallEtale.precoverage B S hS F E := by
    rw [SmallEtale.mem_precoverage_iff]
    refine ⟨PreZeroHypercover.empty E, by simp, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · have := hE'
      simp only [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
        PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_empty, Presieve.map_bot,
        Scheme.fppfPrecoverage]
      exact Scheme.bot_mem_precoverage (@Flat ⊓ @LocallyOfFinitePresentation) _
    · simp
    · have := hE'
      simp only [AlgebraicGeometry.IsEtaleCovering, PreZeroHypercover.presieve₀_map,
        PreZeroHypercover.presieve₀_empty, Presieve.map_bot, Scheme.etalePrecoverage]
      exact Scheme.bot_mem_precoverage (P := @Etale) _
  simpa using (SmallEtale.precoverage B S hS F).generate_mem_toGrothendieck hbotPre

/-- A section of an abelian sheaf on the small étale site over an étale chart with no points
is zero: the empty sieve covers such a chart, so its group of sections is a terminal, hence
zero, object. -/
theorem eq_zero_of_isEmpty_chart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (G : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{w}) (E : SmallEtale B S hS F)
    (hE : IsEmpty ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj E)))
    (σ : G.obj.obj (op E)) : σ = 0 := by
  have hT : IsTerminal (G.obj.obj (op E)) :=
    G.isTerminalOfBotCover E (SmallEtale.bot_mem_topology B S hS F E hE)
  have hid : (𝟙 (G.obj.obj (op E))) = 0 := hT.hom_ext _ _
  have := ConcreteCategory.congr_hom hid σ
  simpa using this

/-- **An abelian sheaf with empty support has only the zero section.** By part (6) of Stacks
04KB the support of a sheaf is the union of the images of the supports of its sections, so a
section of a sheaf with empty support has empty support, its largest open zero locus is
everything, and the section is its own restriction along the identity. -/
theorem eq_zero_of_supportOfSheaf_eq_empty
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (A : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{w})
    (hA : supportOfSheaf B S hS F A = ∅) (U : SmallEtale B S hS F)
    (σ : A.obj.obj (op U)) : σ = 0 := by
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS F hF A] at hA
  have hsec : supportOfSection B S hS F A U σ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
    refine Set.eq_empty_iff_forall_notMem.1 hA
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom y) ?_
    exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨σ, ⟨y, hy, rfl⟩⟩⟩
  have hone : A.obj.map (𝟙 U).op σ = 0 := by
    refine (largestOpenZeroLocus_restrict_iff B S hS F A U σ U (𝟙 U)).2 fun y ↦ ?_
    have hy := Set.eq_empty_iff_forall_notMem.1 hsec y
    simp only [supportOfSection, Set.mem_compl_iff, not_not] at hy
    simpa using hy
  simpa using hone

/-! ### The abelian geometric stalk through the set-valued stalk -/

/-- An object of `AddCommGrpCat` whose underlying type is a subsingleton is a zero object, and
conversely a zero object has a subsingleton underlying type. -/
theorem isZero_addCommGrpCat_iff_subsingleton (M : AddCommGrpCat.{w}) :
    IsZero M ↔ Subsingleton M := by
  refine ⟨fun hM ↦ ⟨fun a b ↦ ?_⟩, fun hM ↦ ?_⟩
  · have hid : (𝟙 M) = 0 := hM.eq_of_src _ _
    have ha : a = 0 := by simpa [AddCommGrpCat.hom_zero] using ConcreteCategory.congr_hom hid a
    have hb : b = 0 := by simpa [AddCommGrpCat.hom_zero] using ConcreteCategory.congr_hom hid b
    rw [ha, hb]
  · have := hM
    exact AddCommGrpCat.isZero_of_subsingleton M

/-- **Forgetting the group structure commutes with the abelian geometric stalk.** Both the
stalk of an abelian presheaf at a geometric point and the stalk of the underlying presheaf of
sets are the fibre at the point of the small étale site determined by that geometric point, and
the forgetful functor of abelian groups preserves the filtered colimit computing it. -/
noncomputable def forgetStalkFunctorIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    stalkFunctor AddCommGrpCat.{u + 1} x ⋙ forget AddCommGrpCat.{u + 1} ≅
      (Functor.whiskeringRight (SmallEtale B S hS F)ᵒᵖ AddCommGrpCat.{u + 1}
          (Type (u + 1))).obj (forget AddCommGrpCat.{u + 1}) ⋙ stalkSetFunctor x :=
  haveI : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  Functor.isoWhiskerRight (etaleSitePointStalkFunctorIso B S hS F x hF).symm
      (forget AddCommGrpCat.{u + 1}) ≪≫
    ((etaleSitePoint B S hS F x hF).presheafFiberCompIso
      (forget AddCommGrpCat.{u + 1})).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleSitePointStalkIso B S hS F x hF)

/-- The abelian stalk of a presheaf of abelian groups at a geometric point vanishes exactly
when the stalk of the underlying presheaf of sets is a subsingleton. -/
theorem isZero_stalkFunctor_iff_subsingleton_stalkSet
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) (P : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj P) ↔
      Subsingleton (stalkSet x (P ⋙ forget AddCommGrpCat.{u + 1})) := by
  have e := (forgetStalkFunctorIso B S hS hF x).app P
  rw [isZero_addCommGrpCat_iff_subsingleton]
  exact ⟨fun h ↦ ⟨fun a b ↦ e.symm.toEquiv.injective (h.elim _ _)⟩,
    fun h ↦ ⟨fun a b ↦ e.toEquiv.injective (h.elim _ _)⟩⟩

/-- The abelian stalk of a sheaf supported on `T` vanishes at a geometric point missing `T`. -/
private theorem isZero_stalkFunctor_of_supportOfSheaf_subset
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (P : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1})
    {T : Set (points B S hS F)} (hsupp : supportOfSheaf B S hS F P ⊆ T)
    (x : GeometricPoint B S hS F) (hx : x.image ∉ T) :
    IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj P.obj) := by
  rw [isZero_stalkFunctor_iff_subsingleton_stalkSet B S hS hF]
  by_contra hns
  exact hx (hsupp ⟨x, rfl, hns⟩)

/-- Transport of invertibility of the image of a morphism along an isomorphism of functors. -/
theorem isIso_map_of_natIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {L R : C ⥤ D} (e : L ≅ R) {A A' : C} (g : A ⟶ A') [IsIso (L.map g)] : IsIso (R.map g) := by
  have h : R.map g = e.inv.app A ≫ L.map g ≫ e.hom.app A' := by
    symm
    rw [e.hom.naturality]
    simp only [← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  rw [h]
  infer_instance

/-- **The abelian geometric stalks are conservative.** A morphism of abelian sheaves on the
small étale site of an algebraic space which is invertible on the stalk at every geometric
point is invertible.

By part (1) of Stacks 04K5 a morphism of sheaves of sets injective on every geometric stalk is
injective on sections over every chart, and by part (2) one surjective on every geometric stalk
is locally surjective; so such a morphism is both a monomorphism and an epimorphism, hence
invertible in the abelian category of abelian sheaves. -/
theorem isIso_of_isIso_stalkFunctor_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {P Q : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}} (φ : P ⟶ Q)
    (h : ∀ x : GeometricPoint B S hS F,
      IsIso ((stalkFunctor AddCommGrpCat.{u + 1} x).map φ.hom)) :
    IsIso φ := by
  set ψ := (sheafCompose (SmallEtale.topology B S hS F)
    (forget AddCommGrpCat.{u + 1})).map φ with hψ
  have hbij : ∀ x : GeometricPoint B S hS F, Function.Bijective (stalkSetMap x ψ.hom) := by
    intro x
    have h1 : IsIso ((stalkFunctor AddCommGrpCat.{u + 1} x ⋙
        forget AddCommGrpCat.{u + 1}).map φ.hom) := by
      have := h x
      exact inferInstanceAs
        (IsIso ((forget AddCommGrpCat.{u + 1}).map ((stalkFunctor _ x).map φ.hom)))
    have := h1
    have h2 : IsIso ((((Functor.whiskeringRight (SmallEtale B S hS F)ᵒᵖ AddCommGrpCat.{u + 1}
        (Type (u + 1))).obj (forget AddCommGrpCat.{u + 1})) ⋙ stalkSetFunctor x).map φ.hom) :=
      isIso_map_of_natIso (forgetStalkFunctorIso B S hS hF x) φ.hom
    exact (isIso_iff_bijective _).1 h2
  have hinj : ∀ U : SmallEtale B S hS F, Function.Injective (ψ.hom.app (op U)) :=
    (injective_iff_stalkSetMap_injective B S hS F hF ψ).2 fun x ↦ (hbij x).1
  have hsurj : Sheaf.IsLocallySurjective ψ :=
    (surjective_iff_stalkSetMap_surjective B S hS F hF ψ).2 fun x ↦ (hbij x).2
  have hmono : Mono φ := by
    refine (sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}).mono_of_mono_map
      ((NatTrans.mono_iff_mono_app _).2 fun U ↦ ?_)
    rw [AddCommGrpCat.mono_iff_injective]
    exact hinj U.unop
  have hepi : Epi φ := by
    have : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS F) φ.hom := by
      rw [Presheaf.isLocallySurjective_iff_whisker_forget]
      exact hsurj
    exact inferInstanceAs (Epi φ)
  exact isIso_of_mono_of_epi φ

/-! ### Base change of a chart along a closed immersion -/

variable {Z X : AlgebraicSpaces B S hS}

/-- The preimage in the point set of an étale chart of `X` of the point set of a morphism
`i : Z ⟶ X`. -/
abbrev chartPreimage (i : Z ⟶ X) (V : SmallEtale B S hS X.1) :
    Set (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) :=
  pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.obj.hom ⁻¹'
    Set.range (pointsMap B S hS Z.1 i.hom)

/-- The preimage of the point set of a closed immersion in the point set of an étale chart is
closed, by Stacks 04CD and continuity of the map induced on point sets. -/
theorem isClosed_chartPreimage (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (V : SmallEtale B S hS X.1) : IsClosed (chartPreimage B S hS i V) :=
  (isClosed_range_pointsMap_of_isClosedImmersion B S hS X.property i.hom hi).preimage
    (continuous_pointsMap B S hS V.obj.hom)

/-- The base change along a morphism of étale charts does not enlarge the preimage of the
point set: a point of a chart over `V` lying over the point set of `i` has image in the
preimage of that point set in `V`. -/
theorem chartPreimage_subset_preimage (i : Z ⟶ X) {V W : SmallEtale B S hS X.1} (f : W ⟶ V) :
    chartPreimage B S hS i W ⊆
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map f)) ⁻¹'
        chartPreimage B S hS i V := by
  intro y hy
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map f) ≫ V.obj.hom = W.obj.hom :=
    CostructuredArrow.w f.hom
  simp only [Set.mem_preimage, chartPreimage] at hy ⊢
  rw [← hw, pointsMap_comp] at hy
  exact hy

/-- An étale chart of `X` whose points avoid the point set of a closed immersion `i : Z ⟶ X`
has empty base change along `i`: by Stacks 03H4 the point set of the base-changed chart is the
preimage of the point set of `i`, and a scheme with no points is empty. -/
theorem isEmpty_smallBaseChange_of_disjoint_range (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (V : SmallEtale B S hS X.1)
    (hV : chartPreimage B S hS i V = ∅) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi).obj V))) := by
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj (hi.pullback V.obj.hom)) (yoneda.map (hi.snd V.obj.hom))) = ∅ := by
    rw [← preimage_range_pointsMap_eq_range_pointsMap_snd B S hS hi V.obj.hom]
    exact hV
  refine ⟨fun z => ?_⟩
  obtain ⟨y, -⟩ := surjective_pointsToScheme B S hS (hi.pullback V.obj.hom) z
  exact absurd (Set.mem_range_self (f := pointsMap B S hS
    (yoneda.obj (hi.pullback V.obj.hom)) (yoneda.map (hi.snd V.obj.hom))) y)
    (by rw [hrange]; exact fun h => h)

/-! ### The small étale direct image of abelian sheaves -/

/-- Abelian sheaves on the small étale site of an algebraic space. -/
abbrev abelianSheaves (Y : AlgebraicSpaces B S hS) :=
  Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}

/-- A section of the direct image of an abelian sheaf along a closed immersion `i : Z ⟶ X`
restricts to zero on every étale chart of `X` whose points avoid the point set of `i`. -/
theorem smallEtaleAbelianPushforward_restrict_eq_zero (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (G : abelianSheaves.{w} B S hS Z)
    {V W : SmallEtale B S hS X.1} (f : W ⟶ V)
    (hW : chartPreimage B S hS i W = ∅)
    (σ : ((smallEtaleAbelianPushforward B S hS i hi).obj G).obj.obj (op V)) :
    ((smallEtaleAbelianPushforward B S hS i hi).obj G).obj.map f.op σ = 0 :=
  eq_zero_of_isEmpty_chart B S hS G ((smallBaseChange B S hS i hi).obj W)
    (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi W hW) _

/-- The complement of the preimage of the point set of a closed immersion is contained in the
largest open zero locus of every section of a direct image along it. -/
theorem compl_chartPreimage_le_largestOpenZeroLocus (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : abelianSheaves.{w} B S hS Z)
    (V : SmallEtale B S hS X.1)
    (σ : ((smallEtaleAbelianPushforward B S hS i hi.rep).obj G).obj.obj (op V)) :
    (⟨(chartPreimage B S hS i V)ᶜ, (isClosed_chartPreimage B S hS i hi V).isOpen_compl⟩ :
        TopologicalSpace.Opens _) ≤
      largestOpenZeroLocus B S hS X.1
        ((smallEtaleAbelianPushforward B S hS i hi.rep).obj G) V σ := by
  refine largestOpenZeroLocus_maximal B S hS X.1 _ V σ _ fun W f hf => ?_
  refine smallEtaleAbelianPushforward_restrict_eq_zero B S hS i hi.rep G f ?_ σ
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
  exact hf y (chartPreimage_subset_preimage B S hS i f hy)

/-- **The support of a small étale direct image.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S` and an abelian sheaf `G` on the small étale site of `Z`, the support
of `i_*G` is contained in the point set of `Z`.

This is Étale Cohomology 04FX transported to algebraic spaces, in the form in which the
essential-image description of Stacks 04E5, part (2) uses it. The support is computed through
its sections description, Stacks 04KB: a point in the support of a section of `i_*G` over a
chart `V` lies outside the largest open zero locus of that section, hence inside the preimage
of the point set of `i`, because charts over `V` avoiding that preimage have empty base change
along `i` and so carry only the zero section. -/
theorem supportOfSheaf_smallEtaleAbelianPushforward_subset (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : abelianSheaves.{w} B S hS Z) :
    supportOfSheaf B S hS X.1 ((smallEtaleAbelianPushforward B S hS i hi.rep).obj G) ⊆
      Set.range (pointsMap B S hS Z.1 i.hom) := by
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.property]
  simp only [Set.iUnion_subset_iff]
  intro V σ y hy
  obtain ⟨v, hv, rfl⟩ := hy
  by_contra hmem
  exact hv ((compl_chartPreimage_le_largestOpenZeroLocus B S hS i hi G V σ) hmem)

/-- **Stacks 04E5, part (2), the essential image: the provable inclusion.** An abelian sheaf
on the small étale site of `X` isomorphic to a direct image along a closed immersion
`i : Z ⟶ X` is supported on the point set of `Z`.

An isomorphism of abelian sheaves is locally surjective, so by part (5) of Stacks 04KB it does
not enlarge the support, and the support of the direct image is bounded by
`AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset`.

Deliberately untagged: Stacks 04E5, part (2) asserts the equivalence of membership in the
essential image with being supported on `|Z|`, and the converse implication is Étale
Cohomology 04CA for algebraic spaces, which this tree does not carry. -/
theorem supportOfSheaf_subset_of_essImage (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (F : abelianSheaves.{w} B S hS X)
    (hF : (smallEtaleAbelianPushforward B S hS i hi.rep).essImage F) :
    supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  intro x hx
  exact supportOfSheaf_smallEtaleAbelianPushforward_subset B S hS i hi G
    (supportOfSheaf_subset_of_isLocallySurjective B S hS X.1 X.property e.hom hx)

/-! ### Geometric points lying on a closed subspace -/

/-- **A geometric point of `X` lying on a closed subspace comes from that subspace.** If the
image of a geometric point `x` of `X` lies in the point set of a closed immersion `i : Z ⟶ X`,
then `x` is the image of a geometric point of `Z` over the same algebraically closed field.

The field spectrum `T` carrying `x` meets `Z` in the base change of `i` along `x`, a closed
subscheme of `T`. It is nonempty: by Stacks 03BU some field-valued extension of `x` and of a
field-valued point of `Z` over the same point of `|X|` exists, and that extension maps into the
base change by its universal property. A nonempty closed subscheme of the spectrum of a field
is the whole spectrum, because the spectrum of a field is a single reduced point, so the base
change of `i` along `x` is an isomorphism; composing its inverse with the projection to `Z`
gives a section of `Z` over `T`, which is the required geometric point. -/
theorem exists_geometricPoint_map_eq_of_mem_range (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Z.1 i.hom)) :
    ∃ z : GeometricPoint B S hS Z.1, geometricPointMap i.hom z = x := by
  obtain ⟨p₀, hp₀⟩ := hx
  obtain ⟨p, rfl⟩ := Quot.exists_rep p₀
  obtain ⟨r, ⟨f, hf⟩, ⟨h, hh⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS X.1
      (FieldValuedPoint.map B S hS Z.1 i.hom p) x.val).1 hp₀
  set g : yoneda.obj x.val.siteObject ⟶ X.1 := yonedaEquiv.symm x.val.value with hgdef
  have hgval : yonedaEquiv g = x.val.value := by
    rw [hgdef]
    exact yonedaEquiv.apply_symm_apply _
  have hsq : (yoneda.map f ≫ (yonedaEquiv.symm p.value :
        yoneda.obj (FieldValuedPoint.siteObject B S hS X.1
          (FieldValuedPoint.map B S hS Z.1 i.hom p)) ⟶ Z.1)) ≫ i.hom
      = yoneda.map h ≫ g := by
    have hps : yonedaEquiv (yonedaEquiv.symm p.value :
        yoneda.obj (FieldValuedPoint.siteObject B S hS X.1
          (FieldValuedPoint.map B S hS Z.1 i.hom p)) ⟶ Z.1) = p.value :=
      yonedaEquiv.apply_symm_apply _
    refine yonedaEquiv.injective ?_
    rw [Category.assoc, ← yonedaEquiv_naturality, ← yonedaEquiv_naturality, yonedaEquiv_comp,
      hps, hgval, hh]
    exact hf
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj (hi.rep.pullback g)) := by
    have hlift : yoneda.obj r.siteObject ⟶ yoneda.obj (hi.rep.pullback g) :=
      (hi.rep.isPullback g).lift
        (yoneda.map f ≫ (yonedaEquiv.symm p.value :
          yoneda.obj (FieldValuedPoint.siteObject B S hS X.1
            (FieldValuedPoint.map B S hS Z.1 i.hom p)) ⟶ Z.1)) (yoneda.map h) hsq
    have hsrc : Nonempty ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
      ⟨(default : Spec (CommRingCat.of r.carrier))⟩
    exact ⟨(BigFppfOver.toScheme B S hS).map (yoneda.preimage hlift) hsrc.some⟩
  have hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) := hi.property_snd g
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj x.val.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of x.val.carrier)))
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj x.val.siteObject) :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of x.val.carrier)))
  have hsurj : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) :=
    ⟨fun y ↦ ⟨hne.some, Subsingleton.elim _ _⟩⟩
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) :=
    isIso_of_isClosedImmersion_of_surjective _
  have : (BigFppfOver.toScheme B S hS).ReflectsIsomorphisms := inferInstance
  have : IsIso (hi.rep.snd g) :=
    isIso_of_reflects_iso (hi.rep.snd g) (BigFppfOver.toScheme B S hS)
  have hzhom : (yoneda.map (inv (hi.rep.snd g)) ≫ hi.rep.fst g) ≫ i.hom = g := by
    rw [Category.assoc, hi.rep.w g, ← Category.assoc, ← yoneda.map_comp, IsIso.inv_hom_id,
      yoneda.map_id, Category.id_comp]
  refine ⟨⟨{ carrier := x.val.carrier, contained := x.val.contained, toBase := x.val.toBase
             value := yonedaEquiv (yoneda.map (inv (hi.rep.snd g)) ≫ hi.rep.fst g) },
    x.property⟩, ?_⟩
  refine Subtype.ext ?_
  change FieldValuedPoint.map B S hS Z.1 i.hom _ = x.val
  have hval : i.hom.app (op x.val.siteObject)
      (yonedaEquiv (yoneda.map (inv (hi.rep.snd g)) ≫ hi.rep.fst g)) = x.val.value := by
    rw [← yonedaEquiv_comp, hzhom, hgval]
  rw [FieldValuedPoint.map]
  congr 1

/-- **An abelian sheaf supported on a closed subspace is detected by the geometric points of
that subspace.** If `A` is supported on the point set of a closed immersion `i : Z ⟶ X` and its
stalk at the image of every geometric point of `Z` is trivial, then its support is empty.

Every geometric point of `X` in the support lies over a point of `|Z|`, hence by
`AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range` is the image of a geometric
point of `Z`, where the stalk is assumed trivial. This is the geometric content of the
`i^{-1}`-half of Stacks 0AEI, isolated from any particular construction of the inverse
image. -/
theorem supportOfSheaf_eq_empty_of_subset_range (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (A : abelianSheaves.{w} B S hS X)
    (hsupp : supportOfSheaf B S hS X.1 A ⊆ Set.range (pointsMap B S hS Z.1 i.hom))
    (hst : ∀ z : GeometricPoint B S hS Z.1,
      Subsingleton (stalkSet (geometricPointMap i.hom z)
        (A.obj ⋙ forget AddCommGrpCat.{w}))) :
    supportOfSheaf B S hS X.1 A = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
  have hyZ : y ∈ Set.range (pointsMap B S hS Z.1 i.hom) := hsupp hy
  obtain ⟨x, hxy, hxs⟩ := hy
  obtain ⟨z, hz⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x (hxy ▸ hyZ)
  exact hxs (hz ▸ hst z)

/-- **The detection criterion for abelian sheaves supported on a closed subspace.** An
abelian sheaf on `X_étale` supported on the point set of a closed immersion `i : Z ⟶ X` and
with trivial stalk at the image of every geometric point of `Z` is zero.

This is the form in which the `i^{-1}`-half of Stacks 0AEI consumes the geometry: given any
identification of the stalk of an inverse image `i^{-1}A` at a geometric point `z` of `Z` with
the stalk of `A` at the image of `z` -- Stacks 04K2, part (4) -- it says that `i^{-1}` is
faithful on the abelian sheaves supported on `|Z|`. -/
theorem eq_zero_of_subset_range_of_stalk (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (A : abelianSheaves.{w} B S hS X)
    (hsupp : supportOfSheaf B S hS X.1 A ⊆ Set.range (pointsMap B S hS Z.1 i.hom))
    (hst : ∀ z : GeometricPoint B S hS Z.1,
      Subsingleton (stalkSet (geometricPointMap i.hom z)
        (A.obj ⋙ forget AddCommGrpCat.{w})))
    (U : SmallEtale B S hS X.1) (σ : A.obj.obj (op U)) : σ = 0 :=
  eq_zero_of_supportOfSheaf_eq_empty B S hS X.property A
    (supportOfSheaf_eq_empty_of_subset_range B S hS i hi A hsupp hst) U σ

/-! ### The essential-image clause of Stacks 04E5, part (2) -/

/-- **Stacks 04FX, the half away from the closed subspace, for abelian sheaves.** The abelian
stalk of a direct image along a closed immersion `i : Z ⟶ X` vanishes at every geometric point
of `X` whose image misses the point set of `Z`. -/
theorem isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom)) :
    IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj
      ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G).obj) := by
  exact isZero_stalkFunctor_of_supportOfSheaf_subset B S hS X.property _
    (supportOfSheaf_smallEtaleAbelianPushforward_subset B S hS i hi G) x hx

/-- **Stacks 04CA, part (2), for algebraic spaces: the essential-image clause.** For a closed
immersion `i : Z ⟶ X` of algebraic spaces over `S`, the unit of the inverse-image/direct-image
adjunction on abelian sheaves is invertible at every abelian sheaf on `X_étale` supported on the
point set of `Z`.

The abelian geometric stalks are conservative, so it suffices to check invertibility stalkwise.
At a geometric point of `X` lying over the point set of `i` the point comes from a geometric
point of `Z`; there the inverse image already carries the unit to an isomorphism, by the
triangle identity and the left-inverse clause of Stacks 04E5, part (2), and the stalk of an
inverse image is the stalk at the image point by part (4) of Stacks 04K2. At a geometric point
whose image misses the point set the stalk of the sheaf vanishes by hypothesis and the stalk of
the direct image vanishes by Stacks 04FX, so any map between them is invertible. -/
theorem isIso_unit_app_of_supportOfSheaf_subset (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (hsupp : supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom)) :
    IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app F) := by
  have hff := fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi
  have := hff.full
  have := hff.faithful
  set pb := smallEtaleAbelianInverseImage B S hS i hi.rep with hpb
  set adj := smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep with hadj
  refine isIso_of_isIso_stalkFunctor_map B S hS X.property (adj.unit.app F) fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS Z.1 i.hom)
  · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x hx
    have hcounit : IsIso (adj.counit.app (pb.obj F)) := by
      rw [hadj]
      infer_instance
    have htri : pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F) = 𝟙 _ :=
      adj.left_triangle_components F
    have hcomp : IsIso (pb.map (adj.unit.app F) ≫ adj.counit.app (pb.obj F)) := by
      rw [htri]
      infer_instance
    have hpull : IsIso (pb.map (adj.unit.app F)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app (pb.obj F))
    have hwhisk : IsIso ((pb ⋙ sheafToPresheaf (SmallEtale.topology B S hS Z.1)
        AddCommGrpCat.{u + 1} ⋙ stalkFunctor AddCommGrpCat.{u + 1} z).map
          (adj.unit.app F)) := by
      have := hpull
      exact inferInstanceAs (IsIso ((stalkFunctor AddCommGrpCat.{u + 1} z).map
        (pb.map (adj.unit.app F)).hom))
    have := hwhisk
    exact isIso_map_of_natIso (smallEtaleAbelianInverseImageStalkIso B S hS i hi.rep z)
      (adj.unit.app F)
  · have hsrc := isZero_stalkFunctor_of_supportOfSheaf_subset B S hS X.property F hsupp x hx
    have htgt : IsZero ((stalkFunctor AddCommGrpCat.{u + 1} x).obj
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj (pb.obj F)).obj) :=
      isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem B S hS i hi (pb.obj F) x hx
    have hmap : (stalkFunctor AddCommGrpCat.{u + 1} x).map (adj.unit.app F).hom =
        (hsrc.iso htgt).hom := hsrc.eq_of_src _ _
    rw [hmap]
    infer_instance

/-- **Stacks 04E5, part (2), the essential image.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S`, an abelian sheaf on the small étale site of `X` lies in the essential
image of the direct image along `i` exactly when its support is contained in the point set
of `Z`.

Both directions are now unconditional: the forward one is
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_essImage`, resting on Étale Cohomology 04FX
for algebraic spaces, and the converse is
`AlgebraicGeometry.Space.isIso_unit_app_of_supportOfSheaf_subset`, Étale Cohomology 04CA for
algebraic spaces, together with the characterization of the essential image of a fully faithful
right adjoint by invertibility of the unit. -/
@[stacks 04E5 "part (2): the essential image"]
theorem smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).essImage F ↔
      supportOfSheaf B S hS X.1 F ⊆ Set.range (pointsMap B S hS Z.1 i.hom) := by
  refine ⟨supportOfSheaf_subset_of_essImage B S hS i hi F, fun h ↦ ?_⟩
  have := isIso_unit_app_of_supportOfSheaf_subset B S hS i hi F h
  exact (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).mem_essImage_of_unit_isIso F

/-- **Stacks 04E5, part (2), the essential-image clause in its sectionwise form.** The unit of
the inverse-image/direct-image adjunction is invertible at every abelian sheaf on `X_étale` all
of whose sections have support in the point set of `Z`.

This is the form `AlgebraicGeometry.Space.UnitIsoOnSupportedSheaves` in which the adjunction
`i_* ⊣ H_Z` of Stacks 0A4M consumes it. By part (6) of Stacks 04KB the support of a sheaf is the
union of the images of the supports of its sections, so the sectionwise hypothesis gives the
containment of the support of the sheaf. -/
theorem unitIsoOnSupportedSheaves_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) : UnitIsoOnSupportedSheaves B S hS i hi := by
  intro F hF
  refine isIso_unit_app_of_supportOfSheaf_subset B S hS i hi F ?_
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.property]
  simp only [Set.iUnion_subset_iff]
  rintro U σ y ⟨v, hv, rfl⟩
  exact hF U σ hv

/-- **The adjunction `i_* ⊣ H_Z` of Stacks 0A4M**, with the essential-image clause
discharged. -/
noncomputable def pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⊣
      sectionsWithSupportInClosedSubspace B S hS i hi :=
  pushforwardSectionsWithSupportAdjunction B S hS i hi
    (unitIsoOnSupportedSheaves_of_isClosedImmersion B S hS i hi)

/-- **The small étale direct image of abelian sheaves along a closed immersion is right
exact.** It is a left adjoint, the right adjoint being the sections with support in `|Z|`. -/
theorem preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    PreservesFiniteColimits (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep) :=
  preservesFiniteColimits_smallEtaleAbelianPushforward_of_adjunction B S hS i hi
    (pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion B S hS i hi)

/-- **Stacks 0A4K for a closed immersion, unconditionally.** The small étale direct image of
abelian sheaves along a closed immersion of algebraic spaces over `S` is exact.

Stacks 0A4K is proved in this development only under an explicit surjectivity hypothesis, the
transport to algebraic spaces of Étale Cohomology 04C2, part (1). For a closed immersion neither
half of exactness needs it: left exactness is right-adjointness of the direct image in the
adjunction with the inverse image, and right exactness is left-adjointness of the direct image
in the adjunction with the sections with support in `|Z|`, whose existence rests on the
essential-image clause proved above. -/
theorem smallEtaleAbelianPushforward_exact_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    exactFunctor (Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep) := by
  rw [exactFunctor_iff]
  exact ⟨inferInstance,
    preservesFiniteColimits_smallEtaleAbelianPushforward_of_isClosedImmersion B S hS i hi⟩

/-! ### The derived category of abelian sheaves and its subcategory of supported complexes -/

attribute [local instance] HasDerivedCategory.standard

/-- Sheafification of presheaves of abelian groups exists on the small étale site of a
presheaf on the big fppf site of `S`, for sections in any universe at least `u + 1`: the site
has its objects in `Type (u + 1)` and its morphisms in `Type u`.

A theorem rather than an instance, as in
`AlgebraicGeometry.Space.smallEtalePushforward_isRightAdjoint_abelian`: at the coefficient
universe `u` the general instances of `AlgebraicGeometry.Space.SmallEtale` already apply, and
an instance tying the coefficients to `max (u + 1) v` hides them. -/
theorem smallEtale_hasSheafify_addCommGrpCat (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{max (u + 1) v} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) v, u, u + 1}
    (SmallEtale.topology B S hS F)

variable (Y : AlgebraicSpaces B S hS)

/-- **The derived category `D(Y_étale)` of abelian sheaves on the small étale site** of an
algebraic space `Y` over `S`. The abelian structure of the sheaves is the one every category
of sheaves with sheafification carries, and the derived category is the standard localization
of the category of cochain complexes at the quasi-isomorphisms. -/
noncomputable abbrev smallEtaleDerivedCategory
    [HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}] :=
  DerivedCategory (abelianSheaves.{w} B S hS Y)

/-- **Stacks 08GF, for abelian sheaves on the small étale site.** An object of
`D(Y_étale)` is *supported on* a subset `T` of `|Y|` when every one of its cohomology sheaves
`Hⁿ(K)` is supported on `T`, the support of an abelian sheaf being
`AlgebraicGeometry.Space.supportOfSheaf` of Stacks 04KA.

As for the `𝒪_Y`-module version `AlgebraicGeometry.Space.CohomologySupportedOn`, the subset is
arbitrary rather than closed: that is the source's notion when `T` is closed, and it applies
directly to the point set of a closed immersion. -/
noncomputable abbrev cohomologySupportedOn
    [HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}]
    (T : Set (points B S hS Y.1)) :
    ObjectProperty (smallEtaleDerivedCategory.{w} B S hS Y) :=
  fun K ↦ ∀ n : ℤ,
    supportOfSheaf B S hS Y.1
      ((DerivedCategory.homologyFunctor (abelianSheaves.{w} B S hS Y) n).obj K) ⊆ T

/-- An object supported on a subset is supported on any larger subset. -/
theorem cohomologySupportedOn.mono
    [HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}]
    {T T' : Set (points B S hS Y.1)} {K : smallEtaleDerivedCategory.{w} B S hS Y}
    (hK : cohomologySupportedOn.{w} B S hS Y T K) (hT : T ⊆ T') :
    cohomologySupportedOn.{w} B S hS Y T' K :=
  fun n ↦ (hK n).trans hT

/-- **The subcategory `D_T(Y_étale)`** of complexes of abelian sheaves on the small étale site
of `Y` whose cohomology sheaves are all supported on a subset `T` of `|Y|`. -/
noncomputable abbrev smallEtaleDerivedCategoryWithSupport
    [HasSheafify (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}]
    (T : Set (points B S hS Y.1)) :=
  (cohomologySupportedOn.{w} B S hS Y T).FullSubcategory

variable {Y}

/-- **The subcategory `D_{|Z|}(X_étale)`** attached to a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S`: the complexes of abelian sheaves on the small étale site of `X`
whose cohomology sheaves are all supported on the point set of `Z`. -/
noncomputable abbrev smallEtaleDerivedCategoryOnClosedSubspace (i : Z ⟶ X)
    [HasSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{w}] :=
  smallEtaleDerivedCategoryWithSupport.{w} B S hS X
    (Set.range (pointsMap B S hS Z.1 i.hom))

/-- A complex of abelian sheaves on `X_étale` all of whose cohomology sheaves are direct
images along a closed immersion `i : Z ⟶ X` lies in `D_{|Z|}(X_étale)`. -/
theorem cohomologySupportedOn_of_essImage_homology (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    [HasSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{w}]
    (K : smallEtaleDerivedCategory.{w} B S hS X)
    (hK : ∀ n : ℤ, (smallEtaleAbelianPushforward B S hS i hi.rep).essImage
      ((DerivedCategory.homologyFunctor (abelianSheaves.{w} B S hS X) n).obj K)) :
    cohomologySupportedOn.{w} B S hS X (Set.range (pointsMap B S hS Z.1 i.hom)) K :=
  fun n ↦ supportOfSheaf_subset_of_essImage B S hS i hi _ (hK n)

end AlgebraicGeometry.Space

end
