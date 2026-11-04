module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward

/-!
# The support of a direct image of modules on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be an
`𝒪_X`-module and let `f_*F` be its direct image `AlgebraicGeometry.Space.modulePushforward`. Then

`Supp(f_*F) ⊆ closure(|f|(Supp F))`,

and for a closed immersion, with `Supp F` closed, the two sides agree:

`Supp(f_*F) = |f|(Supp F)`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_subset_iff_forall_sectionSupportedIn`: the support of
  a module is contained in a given set of points exactly when every section over every étale
  chart is supported in that set.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_of_isClosed`: if `T` is a
  closed set of points of `Y` and the support of `F` lies over `T`, then the support of `f_*F`
  is contained in `T`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_closure`:
  `Supp(f_*F) ⊆ closure(|f|(Supp F))`, with no hypothesis on `f` or on `F`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_image`: for a morphism that
  is closed on points and a module with closed support, `Supp(f_*F) ⊆ |f|(Supp F)`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_subset_preimage`: the support of an
  inverse image is contained in the inverse image of the support.
* `AlgebraicGeometry.Space.image_supportOfSheaf_subset_supportOfSheaf_modulePushforward`: for a
  closed immersion, `|f|(Supp F) ⊆ Supp(f_*F)`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite`:
  for a closed immersion, `Supp(f_*F) = |f|(Supp F)` when `Supp F` is closed, respectively when
  `F` is of finite type on the site.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 085B](https://stacks.math.columbia.edu/tag/085B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The support of a module through its supported sections -/

/-- The support of a module `F` is contained in a set `T` of points exactly when every section
of `F` over every étale chart is supported in `T`, in the sense of
`AlgebraicGeometry.Space.SectionSupportedIn`: the support of the section inside its chart maps
into `T`. -/
theorem supportOfSheaf_subset_iff_forall_sectionSupportedIn (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (T : Set (points B S hS X.1)) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆ T ↔
      ∀ (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)),
        SectionSupportedIn B S hS X.1 X.2 T F W s := by
  rw [supportOfSheaf_eq_iUnion_image_supportOfSection B S hS X.1 X.2
    ((SheafOfModules.toSheaf _).obj F), Set.iUnion_subset_iff]
  refine forall_congr' fun W => ?_
  rw [Set.iUnion_subset_iff]
  exact forall_congr' fun _ => Set.image_subset_iff

/-- If every section of `F` over every étale chart is supported in `T` and also supported in
`T'`, then the subsheaves of sections supported in `T` and in `T'` coincide as submodules of
`F`. -/
theorem supportedSectionsSubmodule_eq_of_forall_sectionSupportedIn
    (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2)
    (T T' : Set (points B S hS X.1))
    (h : ∀ (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)),
      SectionSupportedIn B S hS X.1 X.2 T F W s)
    (h' : ∀ (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)),
      SectionSupportedIn B S hS X.1 X.2 T' F W s) :
    supportedSectionsSubmodule B S hS X.1 X.2 T F =
      supportedSectionsSubmodule B S hS X.1 X.2 T' F :=
  SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W =>
    Submodule.ext fun s => iff_of_true (h W.unop s) (h' W.unop s))

/-- Over an étale chart `W`, the image of the inclusion of the subsheaf of sections of `F`
supported in `T` is the set of sections of `F` over `W` that are supported in `T`. -/
theorem range_supportedSectionsSubmodule_ι (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) :
    Set.range ((supportedSectionsSubmodule B S hS X.1 X.2 T F).ι.val.app (op W)) =
      {s : F.val.obj (op W) | SectionSupportedIn B S hS X.1 X.2 T F W s} := by
  ext s
  refine ⟨?_, fun hs => ⟨⟨s, hs⟩, rfl⟩⟩
  rintro ⟨t, rfl⟩
  exact t.2

/-! ### Every section of a direct image is supported on a closed set over which the module is -/

/-- If, over an étale chart `W`, the subsheaf of sections of `G` supported in `T` has the same
image as the subsheaf of sections supported in the whole point set, then every section of `G`
over `W` is supported in `T`. -/
theorem sectionSupportedIn_of_range_eq (Y : AlgebraicSpaces B S hS)
    (T : Set (points B S hS Y.1)) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1)
    (hW : Set.range ((supportedSectionsSubmodule B S hS Y.1 Y.2 T G).ι.val.app (op W)) =
      Set.range ((supportedSectionsSubmodule B S hS Y.1 Y.2 Set.univ G).ι.val.app (op W)))
    (s : G.val.obj (op W)) :
    SectionSupportedIn B S hS Y.1 Y.2 T G W s := by
  have hs : s ∈ Set.range ((supportedSectionsSubmodule B S hS Y.1 Y.2 Set.univ
      G).ι.val.app (op W)) := by
    rw [range_supportedSectionsSubmodule_ι]
    exact fun _ _ => Set.mem_univ _
  rwa [← hW, range_supportedSectionsSubmodule_ι] at hs

variable {X Y : AlgebraicSpaces B S hS}

/-- Let `T` be a closed set of points of `Y`. If every section of `F` over every étale chart is
supported in `|f|⁻¹T`, then every section of the direct image of `F` along the morphism of
small étale ringed topoi of `f` is supported in `T`. -/
theorem sectionSupportedIn_pushforwardModules_of_forall (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (T : Set (points B S hS Y.1)) (hT : IsClosed T)
    (h : ∀ (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)),
      SectionSupportedIn B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T) F W s)
    (W : SmallEtale B S hS Y.1)
    (s : (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F).val.obj (op W)) :
    SectionSupportedIn B S hS Y.1 Y.2 T
      (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W s :=
  have htriv : ∀ (W' : SmallEtale B S hS X.1) (t : F.val.obj (op W')),
      SectionSupportedIn B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' Set.univ) F W' t :=
    fun _ _ _ _ => Set.mem_univ _
  have heq := supportedSectionsSubmodule_eq_of_forall_sectionSupportedIn B S hS X F
    (pointsMap B S hS X.1 f.hom ⁻¹' T) (pointsMap B S hS X.1 f.hom ⁻¹' Set.univ) h htriv
  sectionSupportedIn_of_range_eq B S hS Y T _ W
    ((pushforward_supportedSectionsSubmodule_range_eq B S hS f T hT F W).symm.trans
      ((congrArg (fun N : F.Submodule => Set.range
            ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
              N.ι).val.app (op W))) heq).trans
        (pushforward_supportedSectionsSubmodule_range_eq B S hS f Set.univ isClosed_univ F W)))
    s

/-! ### The support of a direct image -/

/-- For a morphism `f : X ⟶ Y` of algebraic spaces, a closed set `T` of points of `Y` and an
`𝒪_X`-module `F` whose support lies in `|f|⁻¹T`, the support of the direct image `f_*F` is
contained in `T`. -/
theorem supportOfSheaf_modulePushforward_subset_of_isClosed (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (T : Set (points B S hS Y.1)) (hT : IsClosed T)
    (hF : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      pointsMap B S hS X.1 f.hom ⁻¹' T) :
    supportOfSheaf B S hS Y.1
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) ⊆ T := by
  rw [← pushforwardModules_eq_modulePushforward B S hS f,
    supportOfSheaf_subset_iff_forall_sectionSupportedIn B S hS Y _ T]
  exact sectionSupportedIn_pushforwardModules_of_forall B S hS f F T hT
    ((supportOfSheaf_subset_iff_forall_sectionSupportedIn B S hS X F _).1 hF)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces and an `𝒪_X`-module `F`,

`Supp(f_*F) ⊆ closure(|f|(Supp F))`. -/
theorem supportOfSheaf_modulePushforward_subset_closure (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) ⊆
      closure (pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) :=
  supportOfSheaf_modulePushforward_subset_of_isClosed B S hS f F _ isClosed_closure
    (Set.image_subset_iff.1 subset_closure)

/-- If the map on points of `f : X ⟶ Y` is closed and the support of the `𝒪_X`-module `F` is
closed, then

`Supp(f_*F) ⊆ |f|(Supp F)`. -/
theorem supportOfSheaf_modulePushforward_subset_image (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hf : IsClosedMorphism B S hS f.hom)
    (hsupp : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))) :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) ⊆
      pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
  supportOfSheaf_modulePushforward_subset_of_isClosed B S hS f F _ (hf _ hsupp)
    (Set.subset_preimage_image _ _)

/-! ### The reverse inclusion for a closed immersion -/

/-- For a morphism `g : X' ⟶ X` of algebraic spaces and an `𝒪_X`-module `F`, the support of
the inverse image `g^*F` is contained in the inverse image under `|g|` of the support of `F`. -/
theorem supportOfSheaf_modulePullback_subset_preimage {X' X : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) ⊆
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  intro pt hpt
  rw [mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X' _ pt] at hpt
  obtain ⟨ybar, hyb, hnt⟩ := hpt
  rw [Set.mem_preimage, mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F]
  refine ⟨geometricPointMap g.hom ybar,
    (geometricPointMap_image g.hom ybar).trans (congrArg _ hyb), ?_⟩
  refine nontrivial_of_nontrivial_extendScalars (etaleLocalRingMap X'.2 g.hom ybar) _ ?_
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (geometricModuleStalkPullbackIso B S hS g ybar F).hom)).nontrivial_congr.1 hnt

/-- For a closed immersion `f : X ⟶ Y` of algebraic spaces and an `𝒪_X`-module `F`,

`|f|(Supp F) ⊆ Supp(f_*F)`. -/
theorem image_supportOfSheaf_subset_supportOfSheaf_modulePushforward (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) := by
  have e : (modulePullback B S hS f).obj ((modulePushforward B S hS f).obj F) ≅ F :=
    (modulePullbackCounitIso B S hS f hf).app F
  rw [Set.image_subset_iff, ← supportOfSheaf_eq_of_iso B S hS X e]
  exact supportOfSheaf_modulePullback_subset_preimage B S hS f _

/-- For a closed immersion `f : X ⟶ Y` of algebraic spaces and an `𝒪_X`-module `F` with closed
support,

`Supp(f_*F) = |f|(Supp F)`. -/
theorem supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hsupp : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))) :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) =
      pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
  subset_antisymm
    (supportOfSheaf_modulePushforward_subset_image B S hS f F
      (isClosedMorphism_of_isClosedImmersion B S hS X.2 Y.2 f.hom hf) hsupp)
    (image_supportOfSheaf_subset_supportOfSheaf_modulePushforward B S hS f hf F)

/-- For a closed immersion `f : X ⟶ Y` of algebraic spaces and an `𝒪_X`-module `F` of finite
type on the small étale site,

`Supp(f_*F) = |f|(Supp F)`. -/
theorem supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsFiniteTypeOnSite F] :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj F)) =
      pointsMap B S hS X.1 f.hom ''
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :=
  supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS f hf F
    (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F)

end AlgebraicGeometry.Space

end
