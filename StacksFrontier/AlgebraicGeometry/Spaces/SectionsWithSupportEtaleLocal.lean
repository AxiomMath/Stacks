module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous

/-!
# Sections with support are étale-local

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`. The inverse image
of abelian sheaves along `f` is restriction along postcomposition of étale charts with `f`: a
chart of `X` is a chart of `Y` with the same underlying scheme, so the sections of `f⁻¹F` over a
chart `U` of `X` are the sections of `F` over the composite chart.

The largest open zero locus of a section, and hence its support, is unchanged by this
identification. Therefore, for a set `T` of points of `Y`, a section of `f⁻¹F` is supported on
`|f|⁻¹ T` exactly when the corresponding section of `F` is supported on `T`, and the subsheaf of
sections with support commutes with inverse image along `f`. For a subspace `Z ⟶ Y` with inverse
image `f⁻¹Z ⟶ X` this gives `f⁻¹ ℋ_Z(F) = ℋ_{f⁻¹Z}(f⁻¹F)` as subsheaves of `f⁻¹F`.

## Main definitions

* `AlgebraicGeometry.Space.etaleAbelianRestriction` — the inverse image of abelian sheaves along
  an étale morphism of algebraic spaces, i.e. restriction along postcomposition of étale charts.

## Main results

* `AlgebraicGeometry.Space.supportOfSection_etaleAbelianRestriction` — the support of a section
  of `f⁻¹F` over a chart of `X` is its support as a section of `F` over the postcomposite chart.
* `AlgebraicGeometry.Space.sectionSupportedOn_etaleAbelianRestriction_iff` — the support
  condition for `|f|⁻¹ T` on `f⁻¹F` is the support condition for `T` on `F`.
* `AlgebraicGeometry.Space.sectionsWithSupportEtaleRestrictionIso` — the subsheaf of sections
  with support commutes with inverse image along an étale morphism, as a natural isomorphism of
  functors.
* `AlgebraicGeometry.Space.sectionsWithSupportEtaleRestrictionIso_hom_app_comp_inclusion` — this
  isomorphism is an identification of subsheaves of `f⁻¹F`.
* `AlgebraicGeometry.Space.closedSectionsWithSupportEtaleRestrictionIso` — the functor `ℋ_Z` on
  the ambient small étale site: for `Z ⟶ Y` with inverse image `f⁻¹Z ⟶ X`, inverse image along
  `f` identifies `ℋ_Z(F)` with `ℋ_{f⁻¹Z}(f⁻¹F)`.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The inverse image of abelian sheaves along an étale morphism of algebraic spaces over `S`:
restriction along postcomposition of étale charts with the morphism. -/
abbrev etaleAbelianRestriction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v} :=
  (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

/-! ### The support of a section is unchanged by étale restriction -/

/-- The largest open zero locus of a section of `f⁻¹F` over an étale chart `U` of `X` is the
largest open zero locus of the corresponding section of `F` over the postcomposite chart of `Y`.
-/
theorem largestOpenZeroLocus_etaleAbelianRestriction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X.1)
    (σ : ((etaleAbelianRestriction.{v} B S hS f hf).obj F).obj.obj (op U)) :
    largestOpenZeroLocus B S hS X.1 ((etaleAbelianRestriction.{v} B S hS f hf).obj F) U σ =
      largestOpenZeroLocus B S hS Y.1 F ((smallEtalePostcomp B S hS f hf).obj U) σ := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨V, g, hzero, y, hy⟩ := hx
    exact ⟨(smallEtalePostcomp B S hS f hf).obj V,
      (smallEtalePostcomp B S hS f hf).map g, hzero, y, hy⟩
  · exact le_zeroImages_of_forall_imageInOpen B S hS X.1
      ((etaleAbelianRestriction.{v} B S hS f hf).obj F) U σ
      (largestOpenZeroLocus B S hS Y.1 F ((smallEtalePostcomp B S hS f hf).obj U) σ)
      (fun V g hg => (largestOpenZeroLocus_restrict_iff B S hS Y.1 F
        ((smallEtalePostcomp B S hS f hf).obj U) σ
        ((smallEtalePostcomp B S hS f hf).obj V)
        ((smallEtalePostcomp B S hS f hf).map g)).2 hg)

/-- **The support of a section is étale-local.** The support of a section of `f⁻¹F` over an étale
chart of `X` is its support as a section of `F` over the postcomposite chart of `Y`. -/
theorem supportOfSection_etaleAbelianRestriction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X.1)
    (σ : ((etaleAbelianRestriction.{v} B S hS f hf).obj F).obj.obj (op U)) :
    supportOfSection B S hS X.1 ((etaleAbelianRestriction.{v} B S hS f hf).obj F) U σ =
      supportOfSection B S hS Y.1 F ((smallEtalePostcomp B S hS f hf).obj U) σ :=
  congrArg (fun W : TopologicalSpace.Opens
      (points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) => W.1ᶜ)
    (largestOpenZeroLocus_etaleAbelianRestriction B S hS f hf F U σ)

/-- The points of a chart of `X` lying over a set `T` of points of `Y` are those lying over its
inverse image in the points of `X`. -/
theorem preimage_pointsMap_smallEtalePostcomp_obj_hom (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (U : SmallEtale B S hS X.1) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj
          ((smallEtalePostcomp B S hS f hf).obj U)))
        ((smallEtalePostcomp B S hS f hf).obj U).obj.hom ⁻¹' T =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom ⁻¹'
        (pointsMap B S hS X.1 f.hom ⁻¹' T) :=
  congrArg (fun g => g ⁻¹' T)
    (pointsMap_comp B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))
      U.obj.hom f.hom)

/-- A section of `f⁻¹F` over an étale chart of `X` is supported on the inverse image of a set `T`
of points of `Y` exactly when the corresponding section of `F` over the postcomposite chart is
supported on `T`. -/
theorem sectionSupportedOn_etaleAbelianRestriction_iff (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1))
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v})
    (U : SmallEtale B S hS X.1)
    (σ : ((etaleAbelianRestriction.{v} B S hS f hf).obj F).obj.obj (op U)) :
    SectionSupportedOn B S hS X.1 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleAbelianRestriction.{v} B S hS f hf).obj F) U σ ↔
      SectionSupportedOn B S hS Y.1 T F ((smallEtalePostcomp B S hS f hf).obj U) σ := by
  unfold SectionSupportedOn
  rw [supportOfSection_etaleAbelianRestriction B S hS f hf F U σ,
    preimage_pointsMap_smallEtalePostcomp_obj_hom B S hS f hf T U]
  exact Iff.rfl

/-! ### Sections with support commute with étale restriction -/

/-- The subsheaf of sections with support in a set `T` of points of `Y` commutes with inverse
image along an étale morphism. -/
def sectionsWithSupportSheafEtaleRestrictionIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1))
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v}) :
    (etaleAbelianRestriction.{v} B S hS f hf).obj (sectionsWithSupportSheaf B S hS Y.1 T F) ≅
      sectionsWithSupportSheaf B S hS X.1 (pointsMap B S hS X.1 f.hom ⁻¹' T)
        ((etaleAbelianRestriction.{v} B S hS f hf).obj F) :=
  (fullyFaithfulSheafToPresheaf (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.{v}).preimageIso
    (NatIso.ofComponents
      (fun U => AddEquiv.toAddCommGrpIso
        { toFun := fun σ =>
            ⟨σ.1, (sectionSupportedOn_etaleAbelianRestriction_iff
              B S hS f hf T F U.unop σ.1).2 σ.2⟩
          invFun := fun σ =>
            ⟨σ.1, (sectionSupportedOn_etaleAbelianRestriction_iff
              B S hS f hf T F U.unop σ.1).1 σ.2⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl
          map_add' := fun _ _ => Subtype.ext rfl })
      (fun _ => by ext; rfl))

/-- **Sections with support commute with étale restriction**, as a natural isomorphism of
functors from abelian sheaves on `Y_étale` to abelian sheaves on `X_étale`. -/
def sectionsWithSupportEtaleRestrictionIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) :
    sectionsWithSupport.{v} B S hS Y.1 T ⋙ etaleAbelianRestriction.{v} B S hS f hf ≅
      etaleAbelianRestriction.{v} B S hS f hf ⋙
        sectionsWithSupport.{v} B S hS X.1 (pointsMap B S hS X.1 f.hom ⁻¹' T) :=
  NatIso.ofComponents (sectionsWithSupportSheafEtaleRestrictionIso B S hS f hf T)
    (fun _ => by refine Sheaf.hom_ext ?_; ext U σ; rfl)

/-- The comparison isomorphism is an identification of subsheaves of `f⁻¹F`: it is compatible
with the inclusions of the sections with support into the ambient sheaf. -/
theorem sectionsWithSupportEtaleRestrictionIso_hom_app_comp_inclusion
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (T : Set (points B S hS Y.1))
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{v}) :
    (sectionsWithSupportEtaleRestrictionIso.{v} B S hS f hf T).hom.app F ≫
        sectionsWithSupportSheafInclusion B S hS X.1 (pointsMap B S hS X.1 f.hom ⁻¹' T)
          ((etaleAbelianRestriction.{v} B S hS f hf).obj F) =
      (etaleAbelianRestriction.{v} B S hS f hf).map
        (sectionsWithSupportSheafInclusion B S hS Y.1 T F) := by
  refine Sheaf.hom_ext ?_
  ext U σ
  rfl

/-! ### The functor `ℋ_Z` of a closed subspace -/

/-- Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over `S`, let `Z ⟶ Y` be a
subspace and let `f⁻¹Z ⟶ X` be its inverse image, presented by the cartesian square `hk`. Then
inverse image along `f` identifies the sections with support in `Z` of an abelian sheaf `F` on
`Y_étale` with the sections with support in `f⁻¹Z` of `f⁻¹F`:
`f⁻¹ ℋ_Z(F) = ℋ_{f⁻¹Z}(f⁻¹F)` as subsheaves of `f⁻¹F` on `X_étale`. -/
@[stacks 0A4P "degree zero, on the ambient site: f⁻¹ H_Z(F) = H_{f⁻¹Z}(f⁻¹F)"]
def closedSectionsWithSupportEtaleRestrictionIso {W Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y) (iX : W ⟶ X) (k : W ⟶ Z)
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    closedSectionsWithSupport.{v} B S hS iY ⋙ etaleAbelianRestriction.{v} B S hS f hf ≅
      etaleAbelianRestriction.{v} B S hS f hf ⋙ closedSectionsWithSupport.{v} B S hS iX :=
  haveI hrange : Set.range (pointsMap B S hS W.1 iX.hom) =
      pointsMap B S hS X.1 f.hom ⁻¹' Set.range (pointsMap B S hS Z.1 iY.hom) := by
    simpa using (preimage_image_pointsMap_of_isPullback B S hS hk Set.univ).symm
  (sectionsWithSupportEtaleRestrictionIso.{v} B S hS f hf
      (Set.range (pointsMap B S hS Z.1 iY.hom))).trans
    (Functor.isoWhiskerLeft (etaleAbelianRestriction.{v} B S hS f hf)
      (eqToIso (congrArg (sectionsWithSupport.{v} B S hS X.1) hrange.symm)))

end AlgebraicGeometry.Space

end
