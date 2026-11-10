module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupport

/-!
# Injectivity of the sections with support in a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes and let `ℐ` be an injective abelian sheaf on
`X_étale`.  The sections of `ℐ` with support in `Z`, viewed on `Z_étale`, form an injective
abelian sheaf `ℋ_Z(ℐ)`.  The reason is that `ℋ_Z` is right adjoint to the exact functor `i_*`:
a section of `i_*𝒢` has support in `Z`, so a map `i_*𝒢 ⟶ ℱ` is the same as a map into the
subsheaf of sections with support in `Z`; that subsheaf is itself a direct image from `Z`, so
by full faithfulness such a map is the same as a map `𝒢 ⟶ ℋ_Z(ℱ)` on `Z_étale`.

## Main results

* `AlgebraicGeometry.injective_supportedSections_obj` — the sections with support in a closed
  subscheme of an injective abelian sheaf form an injective abelian sheaf on that subscheme.

## Implementation notes

Two vanishing statements over the open complement `j` drive the proof.  The restriction
`j^{-1}i_*𝒢` vanishes because the stalks of `i_*𝒢` vanish away from the closed subscheme; this
makes a map out of `i_*𝒢` factor through the sections with support in `Z`.  The restriction
`j^{-1}ℋ_Z(ℱ)` vanishes because `j^{-1}` is left exact while the unit `ℱ ⟶ j_*j^{-1}ℱ` becomes
a split monomorphism after restricting to the complement; this puts the subsheaf of sections
with support in `Z` into the essential image of `i_*`, which is what identifies maps into it
with maps on `Z_étale`.

## References

* [Stacks Project, Tag 09XQ](https://stacks.math.columbia.edu/tag/09XQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The value at an object of the kernel of a natural transformation is the kernel of its
component at that object: limits in a functor category are computed pointwise. -/
public def kernelObjIso {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) (A : C) : (kernel η).obj A ≅ kernel (η.app A) :=
  asIso (kernelComparison η ((evaluation C D).obj A))

/-- A map whose composition with the component of a natural transformation vanishes factors
through the value there of the kernel of that transformation. -/
private theorem exists_factor_kernel_ι_app {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Abelian D] {F G : C ⥤ D} (η : F ⟶ G) (A : C) {W : D}
    (φ : W ⟶ F.obj A) (hφ : φ ≫ η.app A = 0) :
    ∃ ψ : W ⟶ (kernel η).obj A, ψ ≫ (kernel.ι η).app A = φ := by
  have hι : (kernelObjIso η A).inv ≫ (kernel.ι η).app A = kernel.ι (η.app A) := by
    rw [Iso.inv_comp_eq]
    exact (kernelComparison_comp_ι η ((evaluation C D).obj A)).symm
  refine ⟨kernel.lift (η.app A) φ hφ ≫ (kernelObjIso η A).inv, ?_⟩
  rw [Category.assoc, hι, kernel.lift_ι]

/-- An object is injective as soon as it is the inverse image of an object `A` carrying an
invertible adjunction unit and admitting a monomorphism `ι` into an injective object through
which every map from a direct image factors.

Mapping a monomorphism forward keeps it monic, a map into the inverse image of `A` becomes a
map into `A` through the invertible unit, and the factorisation hypothesis turns an extension
into the injective object into an extension into `A`; full faithfulness of the direct image
brings that extension back. -/
private theorem injective_obj_of_unit_isIso {C D : Type*} [Category* C] [Category* D]
    {pullbackFunctor : C ⥤ D} {pushforwardFunctor : D ⥤ C}
    (adj : pullbackFunctor ⊣ pushforwardFunctor)
    [pushforwardFunctor.Full] [pushforwardFunctor.Faithful]
    [pushforwardFunctor.PreservesMonomorphisms]
    {A I : C} (ι : A ⟶ I) (hι : Mono ι) (hI : Injective I)
    (hfactor : ∀ (G : D) (φ : pushforwardFunctor.obj G ⟶ I),
      ∃ ψ : pushforwardFunctor.obj G ⟶ A, ψ ≫ ι = φ)
    (hunit : IsIso (adj.unit.app A)) :
    Injective (pullbackFunctor.obj A) := by
  have := hι
  have := hI
  constructor
  intro G G' g f hf
  obtain ⟨χ, hχ⟩ := Injective.factors
    ((pushforwardFunctor.map g ≫ inv (adj.unit.app A)) ≫ ι) (pushforwardFunctor.map f)
  obtain ⟨ψ, hψ⟩ := hfactor G' χ
  obtain ⟨h, hh⟩ := pushforwardFunctor.map_surjective (ψ ≫ adj.unit.app A)
  refine ⟨h, pushforwardFunctor.map_injective ?_⟩
  have key : pushforwardFunctor.map f ≫ ψ =
      pushforwardFunctor.map g ≫ inv (adj.unit.app A) := by
    rw [← cancel_mono ι, Category.assoc, hψ, hχ]
  rw [pushforwardFunctor.map_comp, hh, ← Category.assoc, key, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- Inverse image of abelian sheaves on the small étale sites along a morphism of `B`-schemes,
the left adjoint of the direct image `AlgebraicGeometry.SmallEtale.etalePushforward`. -/
public abbrev smallEtalePullbackAbOfScheme :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B Z :=
  (smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)

/-- **Direct image of abelian sheaves along the closed immersion**, `i_*`.

It is public because the statement of [Stacks, Tag 0A45] in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportTriangle` names it: the
cohomology sheaves with support in the closed subscheme appear there pushed forward along
`i`. -/
public abbrev smallEtaleClosedPushforward :
    SmallEtaleAbelianSheaf B Z ⥤ SmallEtaleAbelianSheaf B X :=
  (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)

/-- Direct image of abelian sheaves along the closed immersion. -/
private abbrev closedPushforward :
    SmallEtaleAbelianSheaf B Z ⥤ SmallEtaleAbelianSheaf B X :=
  smallEtaleClosedPushforward B i

/-- The inverse image/direct image adjunction along the closed immersion. -/
private abbrev closedAdjunction : smallEtalePullbackAbOfScheme B i ⊣ closedPushforward B i :=
  (smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Z.obj Z.property)

/-- Inverse image of abelian sheaves along the inclusion of the open complement. -/
private abbrev complementPullback :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B (closedComplement B i) :=
  (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)

/-- Direct image of abelian sheaves along the inclusion of the open complement. -/
private abbrev complementPushforward :
    SmallEtaleAbelianSheaf B (closedComplement B i) ⥤ SmallEtaleAbelianSheaf B X :=
  (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)

/-- The inverse image/direct image adjunction along the inclusion of the open complement. -/
private abbrev complementAdjunction : complementPullback B i ⊣ complementPushforward B i :=
  (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)

/-- The inclusion of the open complement of a closed immersion has as image the complement of
the image of the closed immersion. -/
private theorem range_closedComplementInclusion :
    Set.range (B.inclusion.map (closedComplementInclusion B i)).base =
      (Set.range (B.inclusion.map i).base)ᶜ := by
  change Set.range (closedComplementOpen B i).ι.base = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- A geometric point of the ambient scheme missing the closed subscheme comes from a geometric
point of the open complement. -/
private theorem exists_geometricPoint_complement (s : GeometricPoint X.obj)
    (hs : s.hom default ∉ Set.range (B.inclusion.map i).base) :
    ∃ t : GeometricPoint (closedComplement B i).obj,
      t.map (B.inclusion.map (closedComplementInclusion B i)) = s := by
  have : IsOpenImmersion (B.inclusion.map (closedComplementInclusion B i)) := by
    change IsOpenImmersion (closedComplementOpen B i).ι
    infer_instance
  have hrange : Set.range s.hom.base ⊆
      Set.range (B.inclusion.map (closedComplementInclusion B i)).base := by
    rw [range_closedComplementInclusion B i]
    rintro y ⟨p, rfl⟩
    rw [show s.hom p = s.hom default from congrArg s.hom.base (Subsingleton.elim _ _)]
    exact hs
  refine ⟨⟨s.residueField, IsOpenImmersion.lift _ s.hom hrange⟩, ?_⟩
  have heq : (⟨s.residueField, IsOpenImmersion.lift
      (B.inclusion.map (closedComplementInclusion B i)) s.hom hrange ≫
        B.inclusion.map (closedComplementInclusion B i)⟩ : GeometricPoint X.obj) = s := by
    rw [IsOpenImmersion.lift_fac]
  exact heq

/-- The étale stalk functor at a geometric point is additive: it is the inclusion of sheaves
into presheaves followed by restriction along the pointed neighbourhoods and a colimit, and a
colimit functor is a left adjoint. -/
private instance etaleStalkFunctorAbelian_additive (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) : (etaleStalkFunctorAbelian B S hS s).Additive := by
  have : (colim (J := (geometricPointFiber B S hS s).Elementsᵒᵖ)
      (C := AddCommGrpCat.{u + 1})).Additive := colimConstAdj.left_adjoint_additive
  dsimp only [etaleStalkFunctorAbelian, etaleStalkPresheafFunctor]
  infer_instance

/-- An abelian sheaf whose geometric stalks vanish away from the closed subscheme restricts to
zero on the open complement: every stalk on the complement is a stalk of the given sheaf at a
geometric point missing the closed subscheme, and a sheaf with vanishing stalks is zero. -/
private theorem isZero_complementPullback_obj (H : SmallEtaleAbelianSheaf B X)
    (h : ∀ s : GeometricPoint X.obj, s.hom default ∉ Set.range (B.inclusion.map i).base →
      IsZero (etaleStalk B X.obj X.property s H.obj)) :
    IsZero ((complementPullback B i).obj H) := by
  have hstalk : ∀ t : GeometricPoint (closedComplement B i).obj,
      IsZero ((etaleStalkFunctorAbelian B (closedComplement B i).obj
        (closedComplement B i).property t).obj ((complementPullback B i).obj H)) := by
    intro t
    refine IsZero.of_iso (h _ ?_) ((smallEtalePullbackStalkIsoAbelian B
      (closedComplementInclusion B i) t).app H)
    intro hmem
    have hin : (t.map (B.inclusion.map (closedComplementInclusion B i))).hom default ∈
        Set.range (B.inclusion.map (closedComplementInclusion B i)).base :=
      ⟨t.hom default, by simp [GeometricPoint.map]⟩
    rw [range_closedComplementInclusion B i] at hin
    exact hin hmem
  have hiso : IsIso (0 : (complementPullback B i).obj H ⟶ (complementPullback B i).obj H) := by
    refine isIso_of_isIso_etaleStalkMap.{u, u + 1} B (closedComplement B i).obj
      (closedComplement B i).property 0 fun t => ?_
    rw [show (etaleStalkPresheafFunctor B (closedComplement B i).obj
        (closedComplement B i).property t AddCommGrpCat.{u + 1}).map
          (0 : (complementPullback B i).obj H ⟶ (complementPullback B i).obj H).hom = 𝟙 _ from
      (hstalk t).eq_of_src _ _]
    exact IsIso.id _
  rw [IsZero.iff_id_eq_zero]
  simpa using (IsIso.inv_hom_id (0 : (complementPullback B i).obj H ⟶
    (complementPullback B i).obj H)).symm

/-- An abelian sheaf restricting to zero on the open complement has support inside the closed
subscheme: a geometric point missing the closed subscheme comes from the complement, and there
the stalk is a stalk of the vanishing restriction. -/
private theorem supportSheaf_subset_of_isZero_complementPullback
    (H : SmallEtaleAbelianSheaf B X) (hH : IsZero ((complementPullback B i).obj H)) :
    SmallEtale.supportSheaf B X.obj X.property H ⊆ Set.range (B.inclusion.map i).base := by
  rintro x ⟨s, hs, hnonzero⟩
  by_contra hx
  obtain ⟨t, rfl⟩ := exists_geometricPoint_complement B i s (by rwa [hs])
  exact hnonzero (IsZero.of_iso ((etaleStalkFunctorAbelian B
    (closedComplement B i).obj (closedComplement B i).property t).map_isZero hH)
    ((smallEtalePullbackStalkIsoAbelian B (closedComplementInclusion B i) t).app H).symm)

/-- The restriction to the open complement of a direct image from the closed subscheme
vanishes, since the stalks of that direct image vanish away from the closed subscheme. -/
private theorem isZero_complementPullback_pushforward (G : SmallEtaleAbelianSheaf B Z) :
    IsZero ((complementPullback B i).obj ((closedPushforward B i).obj G)) :=
  isZero_complementPullback_obj B i _ fun s hs =>
    smallEtalePushforward_stalk_isZero_of_not_mem_range B i G s hs

/-- The restriction map to the open complement vanishes on a direct image from the closed
subscheme, because that direct image restricts to zero there. -/
public theorem complementRestriction_app_smallEtaleClosedPushforward
    (G : SmallEtaleAbelianSheaf B Z) :
    (complementRestriction B i).app
      (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).obj G) = 0 :=
  ((complementPushforward B i).map_isZero
    (isZero_complementPullback_pushforward B i G)).eq_of_tgt _ _

/-- The same vanishing, for the file-local spelling of the direct image. -/
private theorem complementRestriction_app_pushforward (G : SmallEtaleAbelianSheaf B Z) :
    (complementRestriction B i).app ((closedPushforward B i).obj G) = 0 :=
  complementRestriction_app_smallEtaleClosedPushforward B i G

/-- A map from a direct image from the closed subscheme into an abelian sheaf factors through
the sections with support in that subscheme: by naturality its composition with the restriction
to the open complement vanishes. -/
private theorem exists_factor_supportedSectionsSubsheaf (F : SmallEtaleAbelianSheaf B X)
    (G : SmallEtaleAbelianSheaf B Z) (φ : (closedPushforward B i).obj G ⟶ F) :
    ∃ ψ : (closedPushforward B i).obj G ⟶ (supportedSectionsSubsheaf B i).obj F,
      ψ ≫ (kernel.ι (complementRestriction B i)).app F = φ := by
  have hzero : φ ≫ (complementRestriction B i).app F = 0 := by
    have hnat := (complementRestriction B i).naturality φ
    rw [complementRestriction_app_pushforward B i G, zero_comp] at hnat
    simpa using hnat
  exact exists_factor_kernel_ι_app (complementRestriction B i) F φ hzero

/-- The sections with support in the closed subscheme restrict to zero on the open complement:
inverse image is left exact, and the restriction map to the complement becomes a split
monomorphism after restricting, so its kernel there vanishes. -/
private theorem isZero_complementPullback_supportedSectionsSubsheaf
    (F : SmallEtaleAbelianSheaf B X) :
    IsZero ((complementPullback B i).obj ((supportedSectionsSubsheaf B i).obj F)) := by
  have hsplit : IsSplitMono
      ((complementPullback B i).map ((complementRestriction B i).app F)) :=
    IsSplitMono.mk'
      { retraction := (complementAdjunction B i).counit.app _
        id := by exact (complementAdjunction B i).left_triangle_components F }
  exact IsZero.of_iso (isZero_kernel_of_mono
    ((complementPullback B i).map ((complementRestriction B i).app F)))
    ((complementPullback B i).mapIso (kernelObjIso (complementRestriction B i) F) ≪≫
      asIso (kernelComparison ((complementRestriction B i).app F) (complementPullback B i)))

/-- An abelian sheaf in the essential image of direct image along the closed immersion has
invertible adjunction unit: the unit at a direct image is inverted by the direct image of the
counit, which is an isomorphism, and the unit is natural. -/
private theorem isIso_unit_of_essImage (H : SmallEtaleAbelianSheaf B X)
    (hH : (closedPushforward B i).essImage H) :
    IsIso ((closedAdjunction B i).unit.app H) := by
  exact ((closedAdjunction B i).isIso_unit_app_iff_mem_essImage).mpr hH

/-- The sections with support in the closed subscheme lie in the essential image of direct
image along the closed immersion, their support being contained in that subscheme. -/
private theorem essImage_supportedSectionsSubsheaf (F : SmallEtaleAbelianSheaf B X) :
    (closedPushforward B i).essImage ((supportedSectionsSubsheaf B i).obj F) := by
  rw [smallEtalePushforward_essImage_iff_abelian]
  exact supportSheaf_subset_of_isZero_complementPullback B i _
    (isZero_complementPullback_supportedSectionsSubsheaf B i F)

/-- The subsheaf of sections with support in a closed subscheme is the direct image of the
abelian sheaf `ℋ_Z` it defines on that subscheme: it lies in the essential image of direct
image, where the unit of the inverse image/direct image adjunction is invertible. -/
public theorem isIso_unit_supportedSectionsSubsheaf (F : SmallEtaleAbelianSheaf B X) :
    IsIso (((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).unit.app
        ((supportedSectionsSubsheaf B i).obj F)) :=
  isIso_unit_of_essImage B i _ (essImage_supportedSectionsSubsheaf B i F)

/-- **Stacks 09XQ.** The sections with support in a closed subscheme of an injective abelian
sheaf on the small étale site of the ambient scheme form an injective abelian sheaf on the
small étale site of that subscheme. -/
@[stacks 09XQ]
public theorem injective_supportedSections_obj (I : SmallEtaleAbelianSheaf B X) [Injective I] :
    Injective ((supportedSections B i).obj I) := by
  have := Functor.preservesMonomorphisms_of_adjunction (closedAdjunction B i)
  exact injective_obj_of_unit_isIso (A := (supportedSectionsSubsheaf B i).obj I) (I := I)
    (closedAdjunction B i) ((kernel.ι (complementRestriction B i)).app I)
    (inferInstance : Mono ((kernel.ι (complementRestriction B i)).app I)) inferInstance
    (exists_factor_supportedSectionsSubsheaf B i I)
    (isIso_unit_supportedSectionsSubsheaf B i I)

end AlgebraicGeometry

end
