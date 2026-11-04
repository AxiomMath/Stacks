module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafColimits
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTransposeIsIso
public import StacksFrontier.CategoryTheory.Adjunction.CompTranspose
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonRestrictionComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedComparisonEtale
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionEtaleIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# The sheaf comparison maps of Stacks 0761 along étale arrows, and étale locality

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` an étale sheaf of
`𝒪_𝒳`-modules. For an arrow `φ : x ⟶ y` of `𝒳` lying over `a : U ⟶ V`, the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is read here in the source's
ambient category, with `a_{small}^*` the inverse image of sheaves of modules
(`AlgebraicGeometry.Stack.restrictSheafPullbackComparison`). This file supplies the three facts
the source's proof of **Stacks 0764** part (3) uses about these maps:

* the composition law of **Stacks 075D** part (1), read on invertibility,
  `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_comp_iff`, for every étale sheaf
  of modules;
* **Stacks 075D** part (2) for modules: `c_χ` is an isomorphism when `χ` lies over an étale
  morphism, `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etale`;
* a morphism of sheaves of modules on the small étale site of `V` which becomes an isomorphism
  after the inverse image along each member of a jointly surjective family of étale morphisms is
  an isomorphism, `AlgebraicGeometry.Stack.isIso_of_forall_isIso_sheafifiedPullbackComparison_map`.

The last two rest on one identification. For an étale `a : U ⟶ V`, composition with `a` is left
adjoint to base change along `a` on the small étale sites
(`AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction`), so the direct image along the
composition is a left adjoint of the direct image along base change on sheaves of modules
(`AlgebraicGeometry.SmallEtale.etalePostcomposePushforwardAdjunction`, from Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` and the two compatibilities of the maps of structure
sheaves). The inverse image `a_{small}^*` of sheaves of modules is another left adjoint of that
functor, so it is the restriction along composition with `a`
(`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonEtaleIso`): its value at an étale `T / U`
is the value at `T / V`. The reflection of isomorphisms then follows from the locality of
invertibility on a site, `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`; and the
étale comparison map, transported across that identification, is computed on sections as the
set-level comparison of **Stacks 075D** part (2), which
`AlgebraicGeometry.Stack.isIso_restrictionInverseImageComparison` proves invertible.

## Main results

* `AlgebraicGeometry.SmallEtale.etalePostcomposePushforwardAdjunction`: restriction along
  composition with an étale `a` is left adjoint to the direct image along base change, on
  sheaves of modules.
* `AlgebraicGeometry.SmallEtale.isIso_of_forall_isIso_etalePostcomposePushforward_map`:
  invertibility of a morphism of sheaves of modules on the small étale site is detected after
  restriction along a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_comp_iff`: **Stacks 075D**
  part (1) for the comparison maps of an étale sheaf of modules, read on invertibility.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etale`: **Stacks 075D**
  part (2) for the comparison maps of an étale sheaf of modules.
* `AlgebraicGeometry.Stack.isIso_of_forall_isIso_sheafifiedPullbackComparison_map`: a morphism
  of sheaves of modules on the small étale site of the scheme below `x` is invertible as soon as
  its inverse images along a family of arrows into `x` over jointly surjective étale morphisms are.

## Implementation notes

The continuity of composition with an étale morphism is supplied by `haveI` rather than found by
instance search: the instance `AlgebraicGeometry.isContinuous_smallEtalePostcompose_ofEtaleHom`
is not found by the discrimination tree at the spelling of the small étale site of the source
which the direct image takes, although it applies. For the same reason of spelling, two
statements comparing the module comparison maps with their adjuncts make
`AlgebraicGeometry.smallEtaleBaseChange`, `CategoryTheory.Over.post`,
`AlgebraicGeometry.Stack.baseStructureSheaf` and `AlgebraicGeometry.Stack.baseRingStructureSheaf`
locally irreducible.

The sheaves of modules have sections in any universe `m` with `UnivLE.{u, m}`, so that the file
applies both at the universe `u` of the schemes and at `u + 1`, where the higher direct images
live. The set-level comparison is taken at the universe `max (u + 1) m` of the sheaf of sets
`F ⋙ forget ⋙ ULift`, which is a universe at which
`AlgebraicGeometry.Stack.isIso_restrictionInverseImageComparison` is stated.

The composition law is used only through invertibility, and is proved in that form: the three
comparison maps are transposes of the direct-image comparisons of **Stacks 06WC**, whose
composition law is a statement about sections, and no isomorphism between the inverse image along
a composite and the composite of the inverse images has to be constructed at section universe
`m`.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t m

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) {U V : E.Scheme} (a : U ⟶ V) [Etale (E.inclusion.map a)]

/-- The map of structure sheaves along composition with an étale morphism `a : U ⟶ V`: the
structure sheaf of the small étale site of `U` at `T` and the structure sheaf of that of `V` at
the composite `T ⟶ U ⟶ V` are the global functions on one scheme, so the map is the identity. -/
noncomputable def etalePostcomposeStructureMap :
    SmallEtale.structureSheaf E U.1 U.property ⟶
      ((smallEtalePostcompose E V.1 V.property
          (SmallEtale.ofEtaleHom E a)).sheafPushforwardContinuous
        RingCat.{u} (SmallEtale.topology E U.1 U.property)
          (SmallEtale.topology E V.1 V.property)).obj
        (SmallEtale.structureSheaf E V.1 V.property) :=
  ObjectProperty.homMk (𝟙 _)

/-- The counit of the adjunction between composition with an étale morphism `a` and base change
along `a`, at `W / V`, is the first projection of the fibre product `W ×_V U`. -/
theorem smallEtalePostcomposeBaseChangeAdjunction_counit_app_hom_left
    (W : SmallEtale E V.1 V.property) :
    ((smallEtalePostcomposeBaseChangeAdjunction E a).counit.app W).hom.left =
      pullback.fst W.obj.hom a := by
  change ((BigEtaleOver.IsEtaleOver E V.1 V.property).ι.map
    ((smallEtalePostcomposeBaseChangeAdjunction E a).counit.app W)).left = _
  dsimp only [smallEtalePostcomposeBaseChangeAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp [Over.mapPullbackAdj_counit_app]
  rfl

/-- The unit of the adjunction between composition with an étale morphism `a` and base change
along `a`, at `T / U`, is a section of the first projection of `T ×_V U`. -/
theorem smallEtalePostcomposeBaseChangeAdjunction_unit_app_hom_left_fst
    (T : SmallEtale E U.1 U.property) :
    ((smallEtalePostcomposeBaseChangeAdjunction E a).unit.app T).hom.left ≫
      pullback.fst ((smallEtalePostcompose E V.1 V.property (SmallEtale.ofEtaleHom E a)).obj
        T).obj.hom a = 𝟙 _ := by
  rw [smallEtalePostcomposeBaseChangeAdjunction_unit_app]
  exact pullback.lift_fst _ _ _

/-- Global functions turn a section of a morphism of the big étale category into a retraction of
the corresponding map of rings. -/
theorem gamma_map_comp_gamma_map_eq_id_of_comp_eq_id {X Y : E.Scheme} (g : X ⟶ Y) (f : Y ⟶ X)
    (hgf : g ≫ f = 𝟙 X) :
    (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map f).op) ≫
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map g).op) = 𝟙 _ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← Functor.map_comp, hgf,
    CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- The first compatibility asked for by `SheafOfModules.pushforwardPushforwardAdj`: restriction of
global functions along the counit of the adjunction between composition with `a` and base change
along `a` is the structure map of `ε_a` followed by the identity. -/
theorem whiskerRight_op_counit_etalePostcompose :
    Functor.whiskerRight (NatTrans.op (smallEtalePostcomposeBaseChangeAdjunction E a).counit)
        (SmallEtale.structureSheaf E V.1 V.property).obj =
      (SmallEtale.smallEtaleStructureMapRing E a).hom ≫
        (smallEtaleBaseChange E a).op.whiskerLeft (etalePostcomposeStructureMap E a).hom := by
  ext W : 2
  induction W using Opposite.rec with | op W => ?_
  change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
      ((smallEtalePostcomposeBaseChangeAdjunction E a).counit.app W).hom.left).op) =
    (SmallEtale.smallEtaleStructureMapRing E a).hom.app (Opposite.op W) ≫ 𝟙 _
  rw [smallEtalePostcomposeBaseChangeAdjunction_counit_app_hom_left,
    smallEtaleStructureMapRing_hom_app]
  exact (Category.comp_id _).symm

/-- The second compatibility asked for by `SheafOfModules.pushforwardPushforwardAdj`: the identity,
followed by the structure map of `ε_a` at a composite and restriction along the unit, is the
identity, the unit being a section of the projection the structure map pulls back along. -/
theorem etalePostcomposeStructureMap_comp_unit :
    (etalePostcomposeStructureMap E a).hom ≫
      (smallEtalePostcompose E V.1 V.property (SmallEtale.ofEtaleHom E a)).op.whiskerLeft
        (SmallEtale.smallEtaleStructureMapRing E a).hom ≫
      Functor.whiskerRight (NatTrans.op (smallEtalePostcomposeBaseChangeAdjunction E a).unit)
        (SmallEtale.structureSheaf E U.1 U.property).obj = 𝟙 _ := by
  ext T : 2
  induction T using Opposite.rec with | op T => ?_
  change 𝟙 _ ≫ (SmallEtale.smallEtaleStructureMapRing E a).hom.app (Opposite.op
      ((smallEtalePostcompose E V.1 V.property (SmallEtale.ofEtaleHom E a)).obj T)) ≫
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (E.inclusion.map
        ((smallEtalePostcomposeBaseChangeAdjunction E a).unit.app T).hom.left).op) = 𝟙 _
  rw [smallEtaleStructureMapRing_hom_app, Category.id_comp]
  exact gamma_map_comp_gamma_map_eq_id_of_comp_eq_id E _ _
    (smallEtalePostcomposeBaseChangeAdjunction_unit_app_hom_left_fst E a T)


/-- Restriction of sheaves of modules along composition with an étale morphism `a : U ⟶ V`, from
the small étale site of `V` to that of `U`: its value at `T / U` is the value at `T / V`. -/
noncomputable abbrev etalePostcomposePushforward (E : BigEtaleSite.{u}) {U V : E.Scheme}
    (a : U ⟶ V) [Etale (E.inclusion.map a)] :
    SheafOfModules.{m} (SmallEtale.structureSheaf E V.1 V.property) ⥤
      SheafOfModules.{m} (SmallEtale.structureSheaf E U.1 U.property) :=
  haveI := isContinuous_smallEtalePostcompose_ofEtaleHom E a
  SheafOfModules.pushforward.{m} (etalePostcomposeStructureMap E a)

/-- **Stacks 03S3, on sheaves of modules.** Restriction along composition with an étale morphism
`a` is left adjoint to the direct image along base change by `a`. This is Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` for the adjunction of sites
`AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction`. -/
noncomputable def etalePostcomposePushforwardAdjunction :
    etalePostcomposePushforward E a ⊣
      SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E a) :=
  haveI := isContinuous_smallEtalePostcompose_ofEtaleHom E a
  haveI : (smallEtaleBaseChange E a).IsContinuous
      (SmallEtale.topology E V.1 V.property) (SmallEtale.topology E U.1 U.property) :=
    smallEtaleBaseChange_isContinuous E a
  SheafOfModules.pushforwardPushforwardAdj (smallEtalePostcomposeBaseChangeAdjunction E a)
    (etalePostcomposeStructureMap E a) (SmallEtale.smallEtaleStructureMapRing E a)
    (whiskerRight_op_counit_etalePostcompose E a) (etalePostcomposeStructureMap_comp_unit E a)

/-- **Invertibility is detected after restriction along a jointly surjective étale family.** A
morphism of sheaves of modules on the small étale site of `V` whose restrictions along
composition with each member of a family of étale morphisms `a i : U i ⟶ V` covering `V` are
invertible is invertible.

The members define objects of the small étale site of `V` covering its final object, and an
object `W` with a map to the member `a i` is the composite of an étale `W ⟶ U i` with `a i`, so
the component at `W` is a component of the restriction along `a i`;
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop` concludes. -/
theorem isIso_of_forall_isIso_etalePostcomposePushforward_map {V : E.Scheme} {I : Type*}
    {U : I → E.Scheme} (a : ∀ i, U i ⟶ V) [∀ i, Etale (E.inclusion.map (a i))]
    (hsurj : ∀ t : E.inclusion.obj V, ∃ i, t ∈ Set.range (E.inclusion.map (a i)))
    {M N : SheafOfModules.{m} (SmallEtale.structureSheaf E V.1 V.property)} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((etalePostcomposePushforward E (a i)).map α)) : IsIso α := by
  let Y : I → SmallEtale E V.1 V.property := fun i => SmallEtale.ofEtaleHom E (a i)
  have hY : (SmallEtale.topology E V.1 V.property).CoversTop Y := by
    refine (GrothendieckTopology.coversTop_iff_of_isTerminal _ _
      (SmallEtale.finalIsTerminal E V.1 V.property) Y).2 ?_
    refine (SmallEtale.topology E V.1 V.property).superset_covering
      (Sieve.ofArrows_le_ofObjects Y
        (fun i => (SmallEtale.finalIsTerminal E V.1 V.property).from (Y i))) ?_
    refine Stacks.EtaleCohomology.ofArrows_mem_topology E V.property Y _ fun t => ?_
    obtain ⟨i, s, hs⟩ := hsurj t
    exact ⟨i, s, by rwa [SmallEtale.toScheme_map_to_final]⟩
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop hY α fun i W g => ?_
  have := isContinuous_smallEtalePostcompose_ofEtaleHom E (a i)
  have hW : Etale (E.inclusion.map g.hom.left) := by
    have hw : E.inclusion.map g.hom.left ≫ E.inclusion.map (a i) = E.inclusion.map W.obj.hom := by
      rw [← E.inclusion.map_comp]
      exact congrArg E.inclusion.map (Over.w g.hom)
    have : Etale (E.inclusion.map g.hom.left ≫ E.inclusion.map (a i)) := by
      rw [hw]
      exact W.property
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ inferInstance this
  let T : SmallEtale E (U i).1 (U i).property := ⟨Over.mk g.hom.left, hW⟩
  have hobj : (smallEtalePostcompose E V.1 V.property (SmallEtale.ofEtaleHom E (a i))).obj T =
      W := by
    obtain ⟨Wo, Wp⟩ := W
    have hw : g.hom.left ≫ a i = Wo.hom := Over.w g.hom
    change (⟨Over.mk (g.hom.left ≫ a i), _⟩ : SmallEtale E V.1 V.property) = ⟨Wo, Wp⟩
    congr 1
    rw [hw]
    rfl
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_congr α
    (congrArg Opposite.op hobj)
    (Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (etalePostcomposeStructureMap E (a i)) α (hα i) (Opposite.op T))

/-- **The direct images of sheaves of modules along the morphisms of ringed sites of
Stacks 070R (2) compose**, at any section universe and at a morphism `c` which is only provably
the composite of `a` and `b`. The direct image along `ε_c` is the direct image along `ε_a`
followed by the one along `ε_b`: both are restriction of sections along the identification
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` of the two successive base changes with
the base change along `c`, which is
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_comparisonComp`. -/
noncomputable def smallEtalePushforwardFactoredCompIsoUnivLE {X Y Z : E.Scheme} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : X ⟶ Z) (hab : a ≫ b = c) :
    SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E c) ≅
      SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E a) ⋙
        SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E b) := by
  subst hab
  exact SheafOfModules.pushforwardCongr₂.{m} _
      (smallEtaleBaseChange_factoredCompIso E X Y Z a b (a ≫ b) rfl)
      (smallEtaleStructureMapRing_comparisonComp E a b) ≪≫
    (SheafOfModules.pushforwardComp.{m} (SmallEtale.smallEtaleStructureMapRing E b)
      (SmallEtale.smallEtaleStructureMapRing E a)).symm

/-- On sections, `AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIsoUnivLE` is
restriction along the identification of the two successive base changes with the base change
along the composite. -/
theorem smallEtalePushforwardFactoredCompIsoUnivLE_hom_app_val_app {X Y Z : E.Scheme} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : X ⟶ Z) (hab : a ≫ b = c)
    (G : SheafOfModules.{m} (SmallEtale.structureSheaf E X.1 X.property))
    (W : (SmallEtale E Z.1 Z.property)ᵒᵖ)
    (n : ((SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E c)).obj
      G).val.obj W) :
    ((smallEtalePushforwardFactoredCompIsoUnivLE E a b c hab).hom.app G).val.app W n =
      G.val.map ((smallEtaleBaseChange_factoredCompIso E X Y Z a b c hab).hom.app W.unop).op n := by
  subst hab
  rfl

end AlgebraicGeometry.SmallEtale

namespace CategoryTheory.Adjunction

/-- **A composition law for transposes, read on invertibility.** Let `adj₁ : L₁ ⊣ R₁`,
`adj₂ : L₂ ⊣ R₂` and `adj : L ⊣ R` be adjunctions with `e : R ≅ R₂ ⋙ R₁`, and let
`f : L₁ X ⟶ Y`, `g : L₂ Y ⟶ Z` and `k : L X ⟶ Z` be morphisms whose transposes satisfy the
composition law `k^♭ ≫ e_Z = f^♭ ≫ R₁(g^♭)`. Then `L₂ f ≫ g` is invertible exactly when `k` is.

The composite `L₂ f ≫ g` is the transpose of `f^♭ ≫ R₁(g^♭)` along the composite adjunction
(`Stacks.CategoryTheory.homEquiv_comp_map_comp`), and transposes of one morphism along two
adjunctions with isomorphic right adjoints are invertible together
(`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_natIsoRight`). No comparison of `L` with
`L₁ ⋙ L₂` has to be named. -/
theorem isIso_map_comp_iff_of_comp_eq {A B C : Type*} [Category A] [Category B] [Category C]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L : A ⥤ C} {R : C ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : R ≅ R₂ ⋙ R₁)
    {X : A} {Y : B} {Z : C} (f : L₁.obj X ⟶ Y) (g : L₂.obj Y ⟶ Z) (k : L.obj X ⟶ Z)
    (hk : adj.homEquiv X Z k ≫ e.hom.app Z =
      adj₁.homEquiv X Y f ≫ R₁.map (adj₂.homEquiv Y Z g)) :
    IsIso (L₂.map f ≫ g) ↔ IsIso k := by
  have h2 := isIso_homEquiv_symm_iff_of_natIsoRight adj (adj₁.comp adj₂) e (adj.homEquiv X Z k)
  rw [Equiv.symm_apply_apply, hk, ← Stacks.CategoryTheory.homEquiv_comp_map_comp adj₁ adj₂ f g,
    Equiv.symm_apply_apply] at h2
  exact h2.symm

end CategoryTheory.Adjunction

namespace Stacks

/-- A map `g : α → β` is bijective as soon as a bijection `f` between the universe lifts of `α`
and `β` lifts it, `f (up a) = up (g a)`. -/
theorem bijective_of_bijective_ulift_map {α β : Type*} (f : ULift.{t} α → ULift.{t} β)
    (g : α → β) (hfg : ∀ a, f (ULift.up a) = ULift.up (g a)) (hf : Function.Bijective f) :
    Function.Bijective g := by
  refine ⟨fun a₁ a₂ ha => ?_, fun b => ?_⟩
  · exact ULift.up_injective (hf.1 (by rw [hfg, hfg, ha]))
  · obtain ⟨z, hz⟩ := hf.2 (ULift.up b)
    exact ⟨z.down, ULift.up_injective ((hfg z.down).symm.trans hz)⟩

end Stacks

namespace Stacks.PresheafOfModules

/-- A morphism into a pushforward followed by the reindexing along an equality of maps of
presheaves of rings acts on sections as the morphism itself. -/
theorem comp_eqToIso_pushforward_hom_app_app_apply_anyUniverse {C D : Type*} [Category C]
    [Category D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {a b : S ⟶ F.op ⋙ R}
    (hab : a = b) {M : PresheafOfModules.{m} S} {N : PresheafOfModules.{m} R}
    (f : M ⟶ (PresheafOfModules.pushforward.{m} a).obj N) (W : Cᵒᵖ) (m : M.obj W) :
    ((f ≫ (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{m} k) hab)).hom.app N).app
      W) m = f.app W m := by
  subst hab
  rfl

/-- **The adjunct of a morphism out of a pullback of presheaves of modules, read at an equal map
of presheaves of rings**, at a universe `m` of the module sections unrelated to the universe of
the rings. Transposing a morphism out of the pullback along `ψ`, precomposed with the comparison
`PresheafOfModules.pullbackCongrUniv` of the pullbacks along `φ = ψ`, along the adjunction at `φ`
is transposing it along the adjunction at `ψ` and reindexing the pushforward along the same
equality. The comparison is the canonical one of two left adjoints of one functor, so this is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` read through the unit. -/
theorem homEquiv_pullbackCongrUniv_hom_app_comp {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {φ ψ : S ⟶ F.op ⋙ R}
    (hφψ : φ = ψ) [(PresheafOfModules.pushforward.{m} φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward.{m} ψ).IsRightAdjoint]
    (X : PresheafOfModules.{m} S) (Y : PresheafOfModules.{m} R)
    (f : (PresheafOfModules.pullback.{m} ψ).obj X ⟶ Y) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{m} φ).homEquiv X Y
        ((PresheafOfModules.pullbackCongrUniv hφψ).hom.app X ≫ f) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{m} ψ).homEquiv X Y f ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{m} k) hφψ.symm)).hom.app Y := by
  rw [Adjunction.homEquiv_naturality_right, PresheafOfModules.pullbackCongrUniv,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply]

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Composition

variable {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)
  [UnivLE.{u, m}]

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf in
/-- **The adjunct of a morphism out of the inverse image of sheaves of modules, on underlying
presheaves, at section universe `m`.** The adjunct of `t` along
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunctionUnivLE` has, as its underlying
morphism of presheaves of modules, the adjunct along the pullback–pushforward adjunction of
presheaves of modules at the map `a_{small}^♯` of **Stacks 06WC** of the sheafification-adjunct
of `t`, followed by the reindexing of the pushforward along
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`.

Three layers are peeled off: the transport along
`AlgebraicGeometry.Stack.pullbackConstructionComparisonIsoUnivLE`, the sheafification bijection,
and the comparison `PresheafOfModules.pullbackCongrUniv` of the two pullbacks of presheaves of
modules, which is the canonical comparison of two left adjoints of one functor. -/
theorem sheafifiedPullbackComparisonAdjunctionUnivLE_homEquiv_val
    (M : SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)))
    (G : SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (t : (sheafifiedPullbackComparisonUnivLE B E h S hS p hp τ hτ φ).obj M ⟶ G) :
    ((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp τ hτ φ).homEquiv M G t).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val
        ((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv _ G t) ≫
      (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{m} k)
        (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing
          B E h S hS p hp τ hτ φ))).hom.app G.val := by
  refine Eq.trans (congrArg (fun k => SheafOfModules.Hom.val k)
    (Adjunction.homEquiv_ofNatIsoLeft_apply
      (SheafOfModules.PullbackConstruction.adjunction.{m}
        (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
      (pullbackConstructionComparisonIsoUnivLE B E h S hS p hp τ hτ φ) t)) ?_
  refine Eq.trans (congrArg
    ((PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)).hom).homEquiv M.val G.val)
    (Adjunction.homEquiv_naturality_left
      (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x)
      ((@PresheafOfModules.pullbackCongrUniv.{m} _ _ _ _ _ _ _ _ _
        (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp τ hτ
          φ).symm inferInstance
        (isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE B E h S hS p hp φ τ
          hτ)).hom.app M.val) t)) ?_
  exact @Stacks.PresheafOfModules.homEquiv_pullbackCongrUniv_hom_app_comp _ _ _ _ _ _ _ _ _ _
    (SmallEtale.presheafPushforward_smallEtaleStructureMapRing_isRightAdjoint_univLE E
      (smallEtaleBaseMorphism B E h S hS p φ))
    (isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE B E h S hS p hp φ τ hτ) _ _ _

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf in
/-- `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunctionUnivLE_homEquiv_val` for a
morphism presented as the one the sheafification bijection produces from a morphism of presheaves
of modules out of the Stacks 06WC pullback, which is how the sheaf comparison maps are built. -/
theorem sheafifiedPullbackComparisonAdjunctionUnivLE_homEquiv_symm_val
    (M : SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)))
    (G : SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (w : (PresheafOfModules.pullback.{m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M.val ⟶ G.val) :
    ((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp τ hτ φ).homEquiv M G
        (((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv _ G).symm w)).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val w ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{m} k)
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing
            B E h S hS p hp τ hτ φ))).hom.app G.val :=
  (sheafifiedPullbackComparisonAdjunctionUnivLE_homEquiv_val B E h S hS p hp τ hτ φ M G _).trans
    (by erw [Equiv.apply_symm_apply])

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf in
/-- The adjunct of the comparison map `c_χ` across the adjunction of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunctionUnivLE` acts on sections as the
comparison of Stacks 06W2 of the underlying presheaf of abelian groups. -/
theorem sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app
    {x' x : 𝒳} (χ : x' ⟶ x)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (W : (SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x))ᵒᵖ)
    (n : ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x).obj F).val.obj W) :
    (((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) χ).homEquiv _ _
          (restrictSheafPullbackComparison B E h S hS p hp χ F)).val.app W) n =
      (restrictionPushforwardComparison B E h S hS p hp χ F.val.presheaf).app W n := by
  have hgval := sheafifiedPullbackComparisonAdjunctionUnivLE_homEquiv_symm_val B E h S hS
    p hp (etaleTopology B) (etaleTopology_le_topology B) χ
    ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x).obj F)
    ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x').obj F)
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp χ (etaleTopology B)
      (etaleTopology_le_topology B) F.val)
  have hadj : (PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (smallEtaleStructureComparison B E h S hS p hp χ (etaleTopology B)
        (etaleTopology_le_topology B))).homEquiv
        ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x).obj F).val
        ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x').obj F).val
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp χ (etaleTopology B)
          (etaleTopology_le_topology B) F.val) =
      restrictModulePushforwardComparison B E h S hS p hp χ (etaleTopology B)
        (etaleTopology_le_topology B) F.val :=
    restrictModulePullbackComparisonUnivLE_adjunct B E h S hS p hp χ (etaleTopology B)
      (etaleTopology_le_topology B) F.val
  have h1 := ConcreteCategory.congr_hom (congrArg (fun k => k.app W) hgval) n
  refine (h1.trans (Stacks.PresheafOfModules.comp_eqToIso_pushforward_hom_app_app_apply_anyUniverse
    (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) χ) _ W n)).trans ?_
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.app W) hadj) n

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf in
/-- **Stacks 075D, part (1), for the comparison maps of an étale sheaf of modules, as a statement
about invertibility.** For arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of `𝒳`, the inverse image along `φ`
of `c_ψ` followed by `c_φ` is invertible exactly when `c_{φ ≫ ψ}` is.

The three comparison maps are the transposes, along the adjunctions of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunctionUnivLE`, of the direct-image
comparisons of **Stacks 06WC**, on sections
(`Stack.sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app`).
Those satisfy the composition law
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_comp` across the identification
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIsoUnivLE` of the direct image
along the composite with the composite of the direct images, and
`CategoryTheory.Adjunction.isIso_map_comp_iff_of_comp_eq` transposes that law to the inverse
images. -/
theorem isIso_restrictSheafPullbackComparison_comp_iff
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsIso ((sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).map
        (restrictSheafPullbackComparison B E h S hS p hp ψ F) ≫
      restrictSheafPullbackComparison B E h S hS p hp φ F) ↔
    IsIso (restrictSheafPullbackComparison B E h S hS p hp (φ ≫ ψ) F) := by
  refine Adjunction.isIso_map_comp_iff_of_comp_eq
    (sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) ψ)
    (sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ)
    (sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (φ ≫ ψ))
    (SmallEtale.smallEtalePushforwardFactoredCompIsoUnivLE E _ _ _
      (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm) _ _ _ ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
  refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun n => ?_)
  have e1 := SmallEtale.smallEtalePushforwardFactoredCompIsoUnivLE_hom_app_val_app E _ _ _
    (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm
    ((restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x).obj F) W
    ((((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (φ ≫ ψ)).homEquiv _ _
        (restrictSheafPullbackComparison B E h S hS p hp (φ ≫ ψ) F)).val.app W) n)
  have e3 := restrictModulePushforwardComparison_app_comp B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ ψ F.val W n
  have e4 := sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app
    B E h S hS p hp ψ F W n
  have e5 := sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app
    B E h S hS p hp φ F ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op.obj W)
    ((restrictionPushforwardComparison B E h S hS p hp ψ F.val.presheaf).app W n)
  refine e1.trans ?_
  rw [sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app]
  refine e3.symm.trans (e5.symm.trans ?_)
  exact (congrArg (fun t => (((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp
    (etaleTopology B) (etaleTopology_le_topology B) φ).homEquiv _ _
      (restrictSheafPullbackComparison B E h S hS p hp φ F)).val.app
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).op.obj W)) t) e4).symm

end Composition

section Etale

variable {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The comparison of Stacks 06W2 is natural in the coefficient category: for a presheaf `F` and
a functor `G`, the comparison for `F ⋙ G` is the image under `G` of the comparison for `F`. Both
are restrictions along one arrow of `𝒳`, by
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app`. -/
theorem restrictionPushforwardComparison_comp_app_smallEtale {x' x : 𝒳} (φ : x' ⟶ x)
    {A A' : Type*} [Category A] [Category A'] (F : 𝒳ᵒᵖ ⥤ A) (G : A ⥤ A')
    (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    (restrictionPushforwardComparison B E h S hS p hp φ (F ⋙ G)).app (Opposite.op W) =
      G.map ((restrictionPushforwardComparison B E h S hS p hp φ F).app (Opposite.op W)) := by
  obtain ⟨φ', h1, h2⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W
  rw [restrictionPushforwardComparison_app B E h S hS p hp φ (F ⋙ G) W φ' h1 h2,
    restrictionPushforwardComparison_app B E h S hS p hp φ F W φ' h1 h2]
  rfl

/-- **Stacks 075D, part (2), on sections.** For an arrow `χ` lying over an étale morphism `a`
and a sheaf of sets `F`, the comparison of Stacks 06W2 at the composite `T ⟶ U ⟶ V`, followed by
restriction along the unit at `T` of the adjunction between composition with `a` and base change
along `a`, is bijective.

This is the transpose of the direct-image comparison across the adjunction of direct images
`AlgebraicGeometry.smallEtalePostcomposePushforwardAdjunction`, which is invertible because the
inverse-image comparison `AlgebraicGeometry.Stack.restrictionInverseImageComparison` is, by
`AlgebraicGeometry.Stack.isIso_restrictionInverseImageComparison`. -/
theorem bijective_restrictionPushforwardComparison_app_comp_map {x' x : 𝒳} (χ : x' ⟶ x)
    (hχ : Etale (B.inclusion.map (p.map χ).left))
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t)))
    (T : SmallEtale E (p.obj x').left.1 (contains_base B E h S hS p x')) :
    haveI := etale_smallEtaleBaseMorphism B E h S hS p χ hχ
    Function.Bijective ((restrictionPushforwardComparison B E h S hS p hp χ F.obj).app
        (Opposite.op ((smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
          (SmallEtale.ofEtaleHom E (smallEtaleBaseMorphism B E h S hS p χ))).obj T)) ≫
      (restrictToSmallEtale B E h S hS p hp x' F.obj).map
        ((smallEtalePostcomposeBaseChangeAdjunction E
          (smallEtaleBaseMorphism B E h S hS p χ)).unit.app T).op) := by
  have := etale_smallEtaleBaseMorphism B E h S hS p χ hχ
  let postAdj := smallEtalePostcomposePushforwardAdjunction E
    (smallEtaleBaseMorphism B E h S hS p χ) (Type (max (u + 1) t))
  let eta : restrictToSmallEtaleSheaf B E h S hS p hp x F ⟶
      E.smallPushforward (smallEtaleBaseMorphism B E h S hS p χ) (Type (max (u + 1) t)) |>.obj
        (restrictToSmallEtaleSheaf B E h S hS p hp x' F) :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp χ F.obj)
  have hg : IsIso ((postAdj.homEquiv _ _).symm eta) :=
    (Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq _ postAdj eta).mp
      (isIso_restrictionInverseImageComparison B E h S hS p hp χ hχ F)
  have happ : IsIso (((postAdj.homEquiv _ _).symm eta).hom.app (Opposite.op T)) := by
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app] at hg
    exact hg _
  rw [Adjunction.homEquiv_counit] at happ
  exact (isIso_iff_bijective _).mp happ

/-- **The inverse image of sheaves of modules along an étale arrow is restriction.** For an
arrow `χ` of `𝒳` lying over an étale morphism `a`, the inverse image `a_{small}^*` of sheaves of
modules is restriction along composition with `a`: both are left adjoints of the direct image
along base change by `a`. -/
noncomputable def sheafifiedPullbackComparisonEtaleIso [UnivLE.{u, m}] {x' x : 𝒳} (χ : x' ⟶ x)
    (hχ : Etale (B.inclusion.map (p.map χ).left)) :
    haveI := etale_smallEtaleBaseMorphism B E h S hS p χ hχ
    sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) χ ≅
      SmallEtale.etalePostcomposePushforward E (smallEtaleBaseMorphism B E h S hS p χ) :=
  haveI := etale_smallEtaleBaseMorphism B E h S hS p χ hχ
  (sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) χ).leftAdjointUniq
    (SmallEtale.etalePostcomposePushforwardAdjunction E (smallEtaleBaseMorphism B E h S hS p χ))

/-- **The inverse images along an étale covering jointly reflect isomorphisms.** Let
`χ i : y i ⟶ x` be arrows of `𝒳` lying over étale morphisms of schemes which are jointly
surjective onto the scheme below `x`. A morphism of sheaves of modules on the small étale site of
that scheme whose inverse images along all the `χ i` are invertible is invertible.

By `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonEtaleIso` each inverse image is the
restriction along composition with the étale morphism below `χ i`, and
`AlgebraicGeometry.SmallEtale.isIso_of_forall_isIso_etalePostcomposePushforward_map` applies. -/
theorem isIso_of_forall_isIso_sheafifiedPullbackComparison_map [UnivLE.{u, m}] {x : 𝒳} {I : Type*}
    {y : I → 𝒳} (χ : ∀ i, y i ⟶ x) (hetale : ∀ i, Etale (B.inclusion.map (p.map (χ i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (χ i)).left))
    {M N : SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x))} (α : M ⟶ N)
    (hα : ∀ i, IsIso ((sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) (χ i)).map α)) : IsIso α := by
  have := fun i => etale_smallEtaleBaseMorphism B E h S hS p (χ i) (hetale i)
  exact SmallEtale.isIso_of_forall_isIso_etalePostcomposePushforward_map E
    (fun i => smallEtaleBaseMorphism B E h S hS p (χ i)) hcov α fun i =>
      (NatIso.isIso_map_iff
        (sheafifiedPullbackComparisonEtaleIso B E h S hS p hp (χ i) (hetale i)) α).mp (hα i)

/-- **Stacks 075D, part (2), for the comparison maps of an étale sheaf of modules.** If an arrow
`χ` of `𝒳` lies over an étale morphism of schemes, the comparison map `c_χ` of an étale sheaf of
modules is an isomorphism.

Across `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonEtaleIso` the map becomes the
transpose, along the adjunction of
`AlgebraicGeometry.SmallEtale.etalePostcomposePushforwardAdjunction`, of the direct-image
comparison; on sections over `T / U` that transpose is the set-level map of
`AlgebraicGeometry.Stack.bijective_restrictionPushforwardComparison_app_comp_map` for the sheaf of
sets of sections, lifted to the universe `max (u + 1) m`, so it is bijective. -/
theorem isIso_restrictSheafPullbackComparison_of_etale [UnivLE.{u, m}] {x' x : 𝒳} (χ : x' ⟶ x)
    (hχ : Etale (B.inclusion.map (p.map χ).left))
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp χ F) := by
  have := etale_smallEtaleBaseMorphism B E h S hS p χ hχ
  let a := smallEtaleBaseMorphism B E h S hS p χ
  let sPCAdj := sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) χ
  let adjP := SmallEtale.etalePostcomposePushforwardAdjunction E a
  let M := (restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x).obj F
  let G := (restrictSheafToSmallEtale.{u, _, _, m} B E h S hS p hp x').obj F
  let g := sPCAdj.homEquiv M G (restrictSheafPullbackComparison B E h S hS p hp χ F)
  have hc : restrictSheafPullbackComparison B E h S hS p hp χ F =
      (Adjunction.leftAdjointUniq adjP sPCAdj).inv.app _ ≫
      (adjP.homEquiv _ _).symm g := by
    rw [← Adjunction.homEquiv_symm_eq_leftAdjointUniq_inv_app_comp adjP sPCAdj g]
    exact (Equiv.symm_apply_apply _ _).symm
  rw [hc]
  suffices hγ : IsIso ((adjP.homEquiv _ _).symm g) from
    IsIso.comp_isIso' ((Adjunction.leftAdjointUniq adjP sPCAdj).app M).isIso_inv hγ
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun T' => ?_
  let Fs : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) m)) :=
    ⟨F.val.presheaf ⋙ forget AddCommGrpCat.{m} ⋙ uliftFunctor.{u + 1, m},
      Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor
        (Presheaf.isSheaf_comp_of_isSheaf _ F.val.presheaf (forget AddCommGrpCat) F.isSheaf)⟩
  let W := Opposite.op ((smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
    (SmallEtale.ofEtaleHom E a)).obj T'.unop)
  let u' := ((smallEtalePostcomposeBaseChangeAdjunction E a).unit.app T'.unop).op
  have key : ∀ n, (((adjP.homEquiv M G).symm g).val.app T') n =
      G.val.map u'
        ((restrictionPushforwardComparison B E h S hS p hp χ F.val.presheaf).app W n) := by
    intro n
    rw [Adjunction.homEquiv_counit]
    exact congrArg (fun t => G.val.map u' t)
      (sheafifiedPullbackComparisonAdjunction_homEquiv_restrictSheafPullbackComparison_app
        B E h S hS p hp χ F W n)
  let φs := (restrictionPushforwardComparison B E h S hS p hp χ Fs.obj).app W ≫
      (restrictToSmallEtale B E h S hS p hp x' Fs.obj).map u'
  have hfun : ∀ n, φs (ULift.up.{u + 1} n) =
      ULift.up.{u + 1} ((((adjP.homEquiv M G).symm g).val.app T') n) := by
    intro n
    exact (congrArg (fun k => (restrictToSmallEtale B E h S hS p hp x' Fs.obj).map u'
      (k (ULift.up.{u + 1} n))) (restrictionPushforwardComparison_comp_app_smallEtale B E h S hS
        p hp χ F.val.presheaf (forget AddCommGrpCat.{m} ⋙ uliftFunctor.{u + 1, m}) W.unop)).trans
      (congrArg ULift.up.{u + 1} (key n)).symm
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (Stacks.bijective_of_bijective_ulift_map _ _ hfun
      (bijective_restrictionPushforwardComparison_app_comp_map.{u, m} B E h S hS p hp χ hχ
        Fs T'.unop))

/-- A property of morphisms of schemes which is invariant under isomorphisms, satisfied by the
underlying morphism of a morphism `k` of the big fppf category over `S`, is satisfied by the
underlying morphism of the image of any arrow lying over `k`: the two differ by isomorphisms. -/
theorem map_left_of_isHomLift {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {U V : BigFppfOver B S hS} (k : V ⟶ U) (hk : P (B.inclusion.map k.left)) {y x : 𝒳}
    (φ : y ⟶ x) [p.IsHomLift k φ] : P (B.inclusion.map (p.map φ).left) := by
  have hleft : (p.map φ).left =
      (eqToHom (IsHomLift.domain_eq p k φ)).left ≫ k.left ≫
        (eqToHom (IsHomLift.codomain_eq p k φ).symm).left := by
    rw [IsHomLift.fac' p k φ]
    rfl
  have hiso : ∀ {a b : BigFppfOver B S hS} (hab : a = b),
      IsIso (B.inclusion.map (eqToHom hab).left) := fun hab => by
    change IsIso ((Over.forget (B.obj hS) ⋙ B.inclusion).map (eqToHom hab))
    infer_instance
  have := hiso (IsHomLift.domain_eq p k φ)
  have := hiso (IsHomLift.codomain_eq p k φ).symm
  rwa [hleft, Functor.map_comp, Functor.map_comp, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]

/-- **The étale-local criterion at one arrow, with the lifts supplied.** Let `φ : x ⟶ y` be an
arrow of `𝒳` lying over a flat morphism of schemes, and let `e i : z i ⟶ y` be arrows lying over
étale morphisms of schemes which are jointly surjective onto the scheme below `y`. Suppose that
every morphism `k` of the big fppf category into the scheme below `z i` with flat underlying
morphism is lifted by some arrow into `z i` at which the comparison map of `F` is an
isomorphism. Then the comparison map `c_φ` of `F` is an isomorphism.

This is the source's proof of **Stacks 0764**, part (3): the fibre product of the scheme
morphisms below `φ` and below `e i` carries a supplied arrow `ψ i` into `z i` over the (flat)
second projection, and an arrow `χ i` into `x` over the (étale) first projection with
`χ i ≫ φ = ψ i ≫ e i`, from the universal property of `φ`. The comparison maps along `ψ i` (by
hypothesis), `e i` and `χ i` (étale, by
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etale`) are isomorphisms, so by
the composition law `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_comp_iff`,
applied twice, the inverse image of `c_φ` along each `χ i` is an isomorphism; the `χ i` lie over a
jointly surjective family of étale morphisms, and
`AlgebraicGeometry.Stack.isIso_of_forall_isIso_sheafifiedPullbackComparison_map` concludes. -/
theorem isIso_restrictSheafPullbackComparison_of_etaleCover_of_lift [UnivLE.{u, m}] {x y : 𝒳}
    (φ : x ⟶ y)
    (hφ : Flat (B.inclusion.map (p.map φ).left)) {I : Type*} {z : I → 𝒳} (e : ∀ i, z i ⟶ y)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (e i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj y).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (e i)).left))
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : ∀ i {V : BigFppfOver B S hS} (k : V ⟶ p.obj (z i)), Flat (B.inclusion.map k.left) →
      ∃ (x' : 𝒳) (φ' : x' ⟶ z i), p.IsHomLift k φ' ∧
        IsIso (restrictSheafPullbackComparison B E h S hS p hp φ' F)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F) := by
  classical
  have key : ∀ i, ∃ (w : 𝒳) (ψ : w ⟶ z i) (χ : w ⟶ x), χ ≫ φ = ψ ≫ e i ∧
      IsIso (restrictSheafPullbackComparison B E h S hS p hp ψ F) ∧
      Etale (B.inclusion.map (p.map χ).left) ∧
      ∀ t : B.inclusion.obj (p.obj x).left, (∃ s, (B.inclusion.map (p.map (e i)).left) s =
        (B.inclusion.map (p.map φ).left) t) →
        t ∈ Set.range (B.inclusion.map (p.map χ).left) := by
    intro i
    have hpb := (IsPullback.of_hasPullback (p.map φ) (p.map (e i))).map
      (BigFppfOver.toScheme B S hS)
    obtain ⟨w, ψ, hψ, hψi⟩ := hF i (pullback.snd (p.map φ) (p.map (e i)))
      (MorphismProperty.of_isPullback hpb hφ)
    have : p.IsStronglyCartesian (p.map φ) φ := hp.isStronglyCartesian φ
    let χ := Functor.IsStronglyCartesian.map p (p.map φ) φ
      (g := pullback.fst (p.map φ) (p.map (e i))) pullback.condition.symm (ψ ≫ e i)
    refine ⟨w, ψ, χ, Functor.IsStronglyCartesian.fac p (p.map φ) φ _ _, hψi,
      map_left_of_isHomLift B S hS p (P := @Etale) _
        (MorphismProperty.of_isPullback hpb.flip (hetale i)) χ,
      fun t ⟨s, hs⟩ => ?_⟩
    refine range_map_left_of_isHomLift B S hS p χ
      (k := pullback.fst (p.map φ) (p.map (e i))) inferInstance ?_
    obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback t s hs.symm
    refine ⟨hpb.isoPullback.inv q, ?_⟩
    change (hpb.isoPullback.inv ≫ (BigFppfOver.toScheme B S hS).map
      (pullback.fst (p.map φ) (p.map (e i)))) q = t
    rw [IsPullback.isoPullback_inv_fst]
    exact hq
  choose w ψ χ hfac hψi hχ hrange using key
  refine isIso_of_forall_isIso_sheafifiedPullbackComparison_map B E h S hS p hp χ hχ
    (fun t => ?_) _ fun i => ?_
  · obtain ⟨i, s, hs⟩ := hcov ((B.inclusion.map (p.map φ).left) t)
    exact ⟨i, hrange i t ⟨s, hs⟩⟩
  · have he := isIso_restrictSheafPullbackComparison_of_etale B E h S hS p hp (e i) (hetale i) F
    have hχi := isIso_restrictSheafPullbackComparison_of_etale B E h S hS p hp (χ i) (hχ i) F
    have hcomp : IsIso (restrictSheafPullbackComparison B E h S hS p hp (ψ i ≫ e i) F) :=
      (isIso_restrictSheafPullbackComparison_comp_iff B E h S hS p hp (ψ i) (e i) F).mp
        inferInstance
    rw [← hfac i] at hcomp
    have hc2 := (isIso_restrictSheafPullbackComparison_comp_iff B E h S hS p hp (χ i) φ F).mpr hcomp
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
      (restrictSheafPullbackComparison B E h S hS p hp (χ i) F) hχi hc2

/-- **The étale-local criterion at one arrow (the argument of Stacks 0764, part (3)).** Let
`φ : x ⟶ y` be an arrow of `𝒳` lying over a flat morphism of schemes, and let `e i : z i ⟶ y` be
arrows lying over étale morphisms of schemes which are jointly surjective onto the scheme below
`y`. If, for every `i`, the comparison map of `F` is an isomorphism at every arrow into `z i`
lying over a flat morphism, then the comparison map `c_φ` of `F` is an isomorphism.

This is `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_etaleCover_of_lift`,
the lifts being supplied by `p` being fibred in groupoids. -/
theorem isIso_restrictSheafPullbackComparison_of_etaleCover [UnivLE.{u, m}] {x y : 𝒳} (φ : x ⟶ y)
    (hφ : Flat (B.inclusion.map (p.map φ).left)) {I : Type*} {z : I → 𝒳} (e : ∀ i, z i ⟶ y)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (e i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj y).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (e i)).left))
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : ∀ i {x' : 𝒳} (φ' : x' ⟶ z i), Flat (B.inclusion.map (p.map φ').left) →
      IsIso (restrictSheafPullbackComparison B E h S hS p hp φ' F)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F) := by
  refine isIso_restrictSheafPullbackComparison_of_etaleCover_of_lift B E h S hS p hp φ hφ e
    hetale hcov F fun i V k hk => ?_
  obtain ⟨x', φ', hφ'⟩ := hp.exists_lift k (z i) rfl
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat)
  exact ⟨x', φ', hφ', hF i φ' (map_left_of_isHomLift B S hS p (P := @Flat) k hk φ')⟩

end Etale

end AlgebraicGeometry.Stack
