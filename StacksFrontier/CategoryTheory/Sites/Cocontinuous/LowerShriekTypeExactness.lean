module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Filtered.AlmostDirected
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Types.Colimits
import StacksFrontier.CategoryTheory.Filtered.SpanCocones
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of lower shriek on sheaves of sets

Let `u : C ⥤ D` be a continuous functor between sites, where `C` has fibre products and
equalizers which `u` preserves. Lower shriek from sheaves of sets on `C` to sheaves of sets on
`D` is then left exact as soon as the images `u X` cover the final object of the topos of `D`.

The covering hypothesis cannot be dropped: lower shriek of the final sheaf is the sheafification
of a presheaf of subsingletons, and that is the final sheaf exactly when those subsingletons are
locally nonempty.

## Main results

* `Stacks.Sites.LowerShriek.sheafPullback_preservesPullbacks`: lower shriek on sheaves of sets
  preserves fibre products.
* `Stacks.Sites.LowerShriek.sheafPullback_preservesTerminal_of_coversTop`: lower shriek carries
  the final sheaf to the final sheaf.
* `Stacks.Sites.LowerShriek.sheafPullback_preservesFiniteLimits_of_coversTop`: lower shriek on
  sheaves of sets is left exact.

## References

* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
* [Stacks Project, Tag 002Y](https://stacks.math.columbia.edu/tag/002Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u vC vD uC uD

namespace Stacks.Sites.LowerShriek

/-- A category with binary products and equalizers is cofiltered-or-empty. -/
theorem isCofilteredOrEmpty_of_products_equalizers
    (C : Type uC) [Category.{vC} C] [HasBinaryProducts C] [HasEqualizers C] :
    IsCofilteredOrEmpty C :=
  ⟨fun X Y => ⟨X ⨯ Y, prod.fst, prod.snd, trivial⟩,
    fun {_ _} f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩⟩

/-- The category indexing the pointwise left Kan extension along `u.op` at an object of the
target is filtered-or-empty, when the source has binary products and equalizers preserved by
`u`. -/
theorem costructuredArrow_isFilteredOrEmpty
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (u : C ⥤ D)
    [HasBinaryProducts C] [HasEqualizers C]
    [PreservesLimitsOfShape (Discrete WalkingPair) u]
    [PreservesLimitsOfShape WalkingParallelPair u] (Y : Dᵒᵖ) :
    IsFilteredOrEmpty (CostructuredArrow u.op Y) :=
  let : IsCofilteredOrEmpty (StructuredArrow Y.unop u) :=
    isCofilteredOrEmpty_of_products_equalizers _
  IsFilteredOrEmpty.of_equivalence (structuredArrowOpEquivalence u Y.unop)

/-- A filtered-or-empty category is almost directed: each of its connected components is
filtered. -/
theorem isAlmostDirected_of_isFilteredOrEmpty
    (C : Type uC) [Category.{vC} C] [IsFilteredOrEmpty C] : IsAlmostDirected C :=
  ⟨isFiltered_component_of_cocone_and_coequaliser (fun {_ Y Z} f g => by
      obtain ⟨W, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs Y Z
      obtain ⟨T, c, hc⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ a) (g ≫ b)
      exact ⟨T, a ≫ c, b ≫ c, by simpa only [Category.assoc] using hc⟩)
    fun {_ _} f g => IsFilteredOrEmpty.cocone_maps f g⟩

/-- A filtered-or-empty colimit of sets, over an essentially small index category, commutes with
fibre products. -/
theorem colim_preservesPullbacks_of_essentiallySmall
    (C : Type uC) [Category.{vC} C] [EssentiallySmall.{u} C] [IsFilteredOrEmpty C]
    [HasColimitsOfShape C (Type u)] :
    PreservesLimitsOfShape WalkingCospan (colim : (C ⥤ Type u) ⥤ Type u) := by
  let e := equivSmallModel.{u} C
  let _ : IsFilteredOrEmpty (SmallModel.{u} C) := IsFilteredOrEmpty.of_equivalence e
  let _ := isAlmostDirected_of_isFilteredOrEmpty (SmallModel.{u} C)
  let _ := preservesLimitsOfShape_colim_of_isConnected (SmallModel.{u} C) WalkingCospan
  exact preservesLimitsOfShape_of_natIso (Functor.Final.colimIso e.inverse)

/-- A filtered-or-empty colimit of subsingletons is a subsingleton. -/
theorem subsingleton_colimit_of_filteredOrEmpty
    {I : Type uC} [Category.{vC} I] [IsFilteredOrEmpty I] (H : I ⥤ Type u)
    [HasColimit H] [∀ i, Subsingleton (H.obj i)] : Subsingleton (colimit H) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨i, a, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨j, b, rfl⟩ := Types.jointly_surjective' y
  obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
  rw [← ConcreteCategory.congr_hom (colimit.w H f) a,
    ← ConcreteCategory.congr_hom (colimit.w H g) b]
  exact congrArg (colimit.ι H k) (Subsingleton.elim _ _)

/-- The left Kan extension of `G` along `L`, taken with its unit, is a pointwise left Kan
extension at every object of the target. -/
noncomputable def lanPointwise
    {A : Type*} [Category A] {E : Type*} [Category E] {H : Type*} [Category H]
    (L : A ⥤ E) (G : A ⥤ H) (X : E)
    [∀ X : E, HasColimitsOfShape (CostructuredArrow L X) H]
    [∀ G : A ⥤ H, L.HasLeftKanExtension G] :
    (Functor.LeftExtension.mk (L.lan.obj G) (L.lanUnit.app G)).IsPointwiseLeftKanExtensionAt X :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := G) _ (L.lanUnit.app G) X

/-- Evaluating the left Kan extension functor along `L` at an object of the target is, naturally
in the functor being extended, the colimit over the costructured-arrow category at that
object. -/
noncomputable def lanEvaluationIsoColim
    {A : Type*} [Category A] {E : Type*} [Category E]
    (H : Type*) [Category H] (L : A ⥤ E) (X : E)
    [∀ X : E, HasColimitsOfShape (CostructuredArrow L X) H]
    [∀ G : A ⥤ H, L.HasLeftKanExtension G] :
    L.lan ⋙ (evaluation E H).obj X ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj L X) ⋙ colim :=
  (NatIso.ofComponents (fun G => (lanPointwise L G X).isoColimit.symm)
    (fun {G₁ G₂} φ => by
      apply colimit.hom_ext
      intro T
      have h₂ := congr_app (L.lanUnit.naturality φ) T.left
      have hd := (L.lan.map φ).naturality T.hom
      dsimp at h₂ hd ⊢
      simp only [ι_colimMap_assoc, Functor.whiskerLeft_app,
        Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_inv,
        Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_inv_assoc,
        Functor.LeftExtension.mk_hom, Functor.LeftExtension.mk_right]
      rw [hd, ← Category.assoc ((L.lanUnit.app G₁).app T.left), ← h₂, Category.assoc]
      rfl)).symm

/-- Lower shriek on sheaves of sets preserves fibre products, when the source site has binary
products and fibre products which the functor preserves. -/
@[sga "4 III 1.3" "Clause 5, special case", sga "4 III 1.9.2" "more general"]
theorem sheafPullback_preservesPullbacks
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) u]
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify K (Type u)]
    [∀ Q : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension Q]
    [∀ Y : Dᵒᵖ, EssentiallySmall.{u} (CostructuredArrow u.op Y)] :
    PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type u) J K) := by
  let _ := hasEqualizers_of_hasPullbacks_and_binary_products (C := C)
  let _ := preservesEqualizers_of_preservesPullbacks_and_binaryProducts u
  let _ (Y : Dᵒᵖ) : HasColimitsOfShape (CostructuredArrow u.op Y) (Type u) :=
    hasColimitsOfShape_of_essentiallySmall.{u} _ _
  let _ (Y : Dᵒᵖ) := costructuredArrow_isFilteredOrEmpty u Y
  let _ : PreservesLimitsOfShape WalkingCospan
      (u.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u)) :=
    preservesLimitsOfShape_of_evaluation _ _ fun Y => by
      let _ := colim_preservesPullbacks_of_essentiallySmall (CostructuredArrow u.op Y)
      exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim (Type u) u.op Y).symm
  let _ : PreservesLimitsOfShape WalkingCospan
      (Functor.sheafPullbackConstruction.sheafPullback u (Type u) J K) :=
    show PreservesLimitsOfShape WalkingCospan
      (sheafToPresheaf J (Type u) ⋙ u.op.lan ⋙ presheafToSheaf K (Type u)) from inferInstance
  exact preservesLimitsOfShape_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u (Type u) J K).symm

/-- Lower shriek on sheaves of sets carries the final sheaf to the final sheaf, when the images
of the objects of the source cover the final object of the topos of `D`. -/
theorem sheafPullback_preservesTerminal_of_coversTop
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasBinaryProducts C] [HasEqualizers C]
    [PreservesLimitsOfShape (Discrete WalkingPair) u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [HasSheafify K (Type u)] [K.WEqualsLocallyBijective (Type u)]
    [∀ Q : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension Q]
    [∀ Y : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow u.op Y) (Type u)]
    (hu : K.CoversTop u.obj) :
    PreservesLimit (Functor.empty.{0} (Sheaf J (Type u)))
      (u.sheafPullback (Type u) J K) := by
  let P := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}
  let Q := (Functor.const Dᵒᵖ).obj PUnit.{u + 1}
  let hQ := Functor.isTerminalConst Dᵒᵖ Types.isTerminalPUnit
  let t : u.op.lan.obj P ⟶ Q := hQ.from _
  have hsub (Y : Dᵒᵖ) : Subsingleton ((u.op.lan.obj P).obj Y) := by
    let _ := costructuredArrow_isFilteredOrEmpty u Y
    let eY : (u.op.lan.obj P).obj Y ≅ colimit (CostructuredArrow.proj u.op Y ⋙ P) :=
      (lanEvaluationIsoColim (Type u) u.op Y).app P
    let _ (i : CostructuredArrow u.op Y) :
        Subsingleton ((CostructuredArrow.proj u.op Y ⋙ P).obj i) :=
      inferInstanceAs (Subsingleton PUnit.{u + 1})
    let _ := subsingleton_colimit_of_filteredOrEmpty (CostructuredArrow.proj u.op Y ⋙ P)
    exact Function.Injective.subsingleton (CategoryTheory.injective_of_mono eY.hom)
  let _ : Presheaf.IsLocallyInjective K t :=
    Presheaf.isLocallyInjective_of_injective K t fun Y _ _ _ => (hsub Y).elim _ _
  let _ : Presheaf.IsLocallySurjective K t := ⟨fun {Y} x => K.superset_covering (by
    rintro Z f ⟨W, ⟨g⟩⟩
    exact ⟨(u.op.lan.obj P).map g.op ((u.op.lanUnit.app P).app (Opposite.op W) PUnit.unit),
      @Subsingleton.elim PUnit.{u + 1} inferInstance _ _⟩) (hu Y)⟩
  have ht : K.W t := (K.W_iff_isLocallyBijective t).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((presheafToSheaf K (Type u)).map t) := (K.W_iff _).mp ht
  have hterminal : IsTerminal ((presheafToSheaf K (Type u)).obj (u.op.lan.obj P)) :=
    (hQ.isTerminalObj (presheafToSheaf K (Type u)) _).ofIso
      (asIso ((presheafToSheaf K (Type u)).map t)).symm
  apply preservesLimit_of_preserves_limit_cone (Sheaf.isTerminalTerminal J Types.isTerminalPUnit)
  refine (isLimitMapConeEmptyConeEquiv _ _).symm ?_
  exact hterminal.ofIso
    ((Functor.sheafPullbackConstruction.sheafPullbackIso u (Type u) J K).app
      (Sheaf.terminal J Types.isTerminalPUnit)).symm

/-- Lower shriek on sheaves of sets is left exact, when the source site has binary products and
fibre products which the functor preserves and the images of its objects cover the final object
of the topos of `D`. -/
theorem sheafPullback_preservesFiniteLimits_of_coversTop
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) u]
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify K (Type u)] [K.WEqualsLocallyBijective (Type u)]
    [∀ Q : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension Q]
    [∀ Y : Dᵒᵖ, EssentiallySmall.{u} (CostructuredArrow u.op Y)]
    (hu : K.CoversTop u.obj) :
    PreservesFiniteLimits (u.sheafPullback (Type u) J K) := by
  let _ := hasEqualizers_of_hasPullbacks_and_binary_products (C := C)
  let _ := preservesEqualizers_of_preservesPullbacks_and_binaryProducts u
  let _ (Y : Dᵒᵖ) : HasColimitsOfShape (CostructuredArrow u.op Y) (Type u) :=
    hasColimitsOfShape_of_essentiallySmall.{u} _ _
  let _ := sheafPullback_preservesPullbacks u J K
  let _ := sheafPullback_preservesTerminal_of_coversTop u J K hu
  let _ := preservesLimitsOfShape_pempty_of_preservesTerminal
    (u.sheafPullback (Type u) J K)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- A continuous functor whose source has binary products and fibre products which it preserves,
and whose images cover the final object of the topos of its target, defines a morphism of sites:
lower shriek is a left exact left adjoint of restriction along it. -/
@[sga "4 VI 7.2.4" "special case"]
theorem isMorphismOfSites_of_coversTop
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) u]
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify K (Type u)] [K.WEqualsLocallyBijective (Type u)]
    [∀ Q : Cᵒᵖ ⥤ Type u, u.op.HasLeftKanExtension Q]
    [∀ Y : Dᵒᵖ, EssentiallySmall.{u} (CostructuredArrow u.op Y)]
    (hu : K.CoversTop u.obj) :
    IsMorphismOfSites.{u} u J K :=
  { toIsContinuous := inferInstance
    hasExactLeftAdjoint := ⟨u.sheafPullback (Type u) J K,
      ⟨u.sheafAdjunctionContinuous (Type u) J K⟩,
      sheafPullback_preservesFiniteLimits_of_coversTop u J K hu⟩ }

end Stacks.Sites.LowerShriek

end
