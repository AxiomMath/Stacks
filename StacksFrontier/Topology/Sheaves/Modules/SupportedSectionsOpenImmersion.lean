module

public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction

/-!
# Excision for the subsheaf of sections with support, on a ringed space

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an open immersion of ringed spaces, let `Z ⊆ X` be a
subset and let `Z' = f^{-1}(Z)`.  Sections with support are local on `X`: pulling the subsheaf
`H_Z(ℱ) ⊆ ℱ` of sections supported on `Z` back along `f` gives the subsheaf
`H_{Z'}(f^*ℱ) ⊆ f^*ℱ` of sections of `f^*ℱ` supported on `Z'`,

`f^*(H_Z ℱ) ≅ H_{Z'}(f^* ℱ)`,

naturally in the `𝒪_X`-module `ℱ`.  That is `supportedSectionsPullbackNatIso`, the main result.
No closedness assumption on `Z` is used.

This is the ringed-space form of
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`, which is stated for a
scheme and an open subscheme.

## Main results

* `suppSection_subset_iff_locally_eq_zero`: a section is supported on `Z` exactly when it
  vanishes on a neighbourhood of each point of its open set outside `Z`.  This replaces every
  appeal to germs below.
* `locallyEqZero_immRestrict_iff`: **the sectionwise engine.**  A section of `ℱ` over the image
  `f(W)` of an open `W ⊆ X'` is supported on `Z` exactly when, read as a section of the
  restriction of `ℱ` along `f` over `W`, it is supported on `Z'`.
* `exists_supportedSectionsImmRestrictIso`: the comparison at a single module, for the concrete
  restriction `immRestrict f` along the open immersion.
* `supportedSectionsImmRestrictNatIso`: that comparison, as an isomorphism of functors.
* `supportedSectionsPullbackNatIso`: the same for the abstract pullback `f^*`.

## Implementation notes

**No germs and no stalk comparison.**  The scheme-level proof compares the germs of a section
read on the open subscheme with its germs on the ambient scheme, through
`AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app`.  There is no ringed-space
counterpart of that comparison in the library, and none is needed: "the support of `s` over `V`
is contained in `Z ∩ V`" is rewritten by `suppSection_subset_iff_locally_eq_zero` as "for every
`x ∈ V` outside `Z` the section `s` restricts to zero on some neighbourhood of `x` inside `V`",
a statement about sections and opens only.  The opens of `X'` contained in `W` correspond to the
opens of `X` contained in `f(W)`, compatibly with restriction of sections, and that is the whole
content of `locallyEqZero_immRestrict_iff`.  Only one inclusion of opens is needed in each
direction, so no equality of opens has to be transported.

**Why `immRestrict`.**  The abstract pullback `RingedSpaceModuleAdjunction.modulePullback f` is
defined as a left adjoint and has no description on sections, so the sectionwise argument cannot
be run against it.  `Stacks.Cohomology.RelativeMayerVietoris.immRestrict f` is the second left
adjoint of `f_*`, whose sections over an open `W` of `X'` are *by definition* the sections of the
module over `f(W)`; the comparison of the two,
`Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback`, carries the result over to
`f^*`.  Every identification used sectionwise below is `rfl`: restriction of scalars does not
change the carrier of a module of sections.

**The comparison is specified, not constructed.**  The subsheaf of sections supported on a
subset is pinned down by `mem_supportedSectionsSheafι_range_iff`, which says that the range of
its inclusion over an open set is exactly the set of sections supported there.  So the
comparison comes from `exists_iso_of_injective_same_range`, which turns two monomorphisms with
the same range into an isomorphism over their common target, and naturality follows from
`natIsoOfMonoOver_naturality` because both subsheaves sit inside the restriction of the
coefficient module.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Definition 17.5.1 (Tag 01AT)](https://stacks.math.columbia.edu/tag/01AT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris

universe u

namespace Stacks.SheafOfModules.SupportedSections

/-! ### Two subsheaves with the same sections -/

/-- **Two sheaves of modules mapping injectively onto the same sections of a third are isomorphic
over it.**  The isomorphism is the identification of the two images.

This is the ringed-space form of
`Stacks.Perfect.SupportedSectionsRestriction.exists_iso_of_injective_same_range`. -/
theorem exists_iso_of_injective_same_range {Y : RingedSpace.{u, u}}
    {A B F : _root_.SheafOfModules.{u} (structureSheafRing Y)} (a : A ⟶ F) (b : B ⟶ F)
    (ha : ∀ V, Function.Injective (a.val.app V))
    (hb : ∀ V, Function.Injective (b.val.app V))
    (hab : ∀ V, Set.range (a.val.app V) = Set.range (b.val.app V)) :
    ∃ e : A ≅ B, e.hom ≫ b = a := by
  let e V : A.val.obj V ≃ₗ[(structureSheafRing Y).obj.obj V] B.val.obj V :=
    (LinearEquiv.ofInjective (a.val.app V).hom (ha V)).trans
      ((LinearEquiv.ofEq _ _ (Submodule.ext fun s => Set.ext_iff.mp (hab V) s)).trans
        (LinearEquiv.ofInjective (b.val.app V).hom (hb V)).symm)
  have he V s : b.val.app V (e V s) = a.val.app V s := by
    change ((LinearEquiv.ofInjective (b.val.app V).hom (hb V)) (e V s)).val = _
    simp [e]
  let ee : A.val ≅ B.val := PresheafOfModules.isoMk (fun V => (e V).toModuleIso) (by
    intro V W j
    ext s
    apply hb W
    change b.val.app W (e W (A.val.map j s)) = b.val.app W (B.val.map j (e V s))
    refine (he W (A.val.map j s)).trans ?_
    exact (PresheafOfModules.naturality_apply a.val j s).trans
      ((congrArg (F.val.map j) (he V s)).symm.trans
        (PresheafOfModules.naturality_apply b.val j (e V s)).symm))
  refine ⟨(_root_.SheafOfModules.fullyFaithfulForget _).preimageIso ee, ?_⟩
  ext V s
  exact he V s

/-- **Componentwise isomorphisms over a common functor assemble into a natural isomorphism**
when the structure maps on one side are monomorphisms: the naturality square commutes because it
does after composing with the monomorphism.

Stated for abstract functors, so that the compositions occurring in the square are the
composition of a single category.  It also gives the naturality of the scheme-level comparison
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`. -/
theorem natIsoOfMonoOver_naturality {C D : Type*} [Category C] [Category D]
    {A B K : C ⥤ D} (a : A ⟶ K) (b : B ⟶ K) (hb : ∀ Y, Mono (b.app Y))
    (e : ∀ Y, A.obj Y ≅ B.obj Y) (he : ∀ Y, (e Y).hom ≫ b.app Y = a.app Y)
    {Y Y' : C} (g : Y ⟶ Y') :
    A.map g ≫ (e Y').hom = (e Y).hom ≫ B.map g := by
  have := hb Y'
  refine (cancel_mono (b.app Y')).1 ?_
  rw [Category.assoc, he, a.naturality, Category.assoc, b.naturality, ← Category.assoc, he]

/-! ### Supported sections, without germs -/

/-- **A section is supported on `Z` exactly when it vanishes near every point of its open set
outside `Z`.**  A germ vanishes exactly when the section already vanishes on a neighbourhood of
the point, by
`AlgebraicGeometry.RingedSpace.ModuleSheaf.sectionGerm_eq_zero_iff`. -/
theorem suppSection_subset_iff_locally_eq_zero {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (V : Opens X.carrier)
    (s : M.val.obj (op V)) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M).suppSection V s ⊆
        Z ∩ (V : Set X.carrier) ↔
      ∀ x ∈ V, x ∉ Z → ∃ (W : Opens X.carrier) (_ : x ∈ W) (j : W ⟶ V),
        M.val.map j.op s = 0 := by
  have hF := (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M).sectionGerm_eq_zero_iff V
  exact ⟨fun h x hx hxZ => (hF x hx s).mp (of_not_not fun hne => hxZ (h ⟨hx, hne⟩).1),
    fun h x ⟨hxV, hne⟩ => ⟨of_not_not fun hxZ => hne ((hF x hxV s).mpr (h x hxV hxZ)), hxV⟩⟩

/-! ### The sectionwise engine -/

/-- A section whose restriction along one map vanishes has vanishing restriction along any
further one.

Stated at a variable ringed space and applied with `exact`: the sections below are sections of a
restriction along an open immersion, equal to sections of the original module only at default
transparency, so a `rw` whose motive abstracts over them is rejected. -/
private theorem map_eq_zero_of_eq_comp {Y : RingedSpace.{u, u}}
    (M : _root_.SheafOfModules.{u} (structureSheafRing Y))
    {A B C : (Opens Y.carrier)ᵒᵖ} (k : A ⟶ C) (i : A ⟶ B) (j : B ⟶ C) (hk : k = i ≫ j)
    (s : M.val.obj A) (hs : M.val.map i s = 0) :
    M.val.map k s = 0 := by
  subst hk
  rw [M.val.map_comp_apply i j s, hs]
  exact map_zero _

section

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [H : SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-- **The sectionwise engine.**  Let `W` be an open of `X'` and let `s` be a section of `ℱ` over
the image `f(W)`, which is the same thing as a section over `W` of the restriction of `ℱ` along
`f`.  Then `s` vanishes near every point of `W` outside `f^{-1}(Z)` exactly when it vanishes
near every point of `f(W)` outside `Z`.

In one direction an open `W₀ ⊆ W` is carried to its image `f(W₀) ⊆ f(W)`; in the other an open
`V ⊆ f(W)` is carried to `f^{-1}(V) ⊓ W`, whose image is contained in `V`, so that the
restriction of `s` to it factors through the restriction of `s` to `V`. -/
theorem locallyEqZero_immRestrict_iff (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (W : Opens X'.carrier) (s : ((immRestrict f).obj M).val.obj (op W)) :
    (∀ x ∈ W, x ∉ ⇑f.hom.base ⁻¹' Z → ∃ (W₀ : Opens X'.carrier) (_ : x ∈ W₀) (j : W₀ ⟶ W),
        ((immRestrict f).obj M).val.map j.op s = 0) ↔
      ∀ y ∈ (immOpensFunctor f).obj W, y ∉ Z → ∃ (V : Opens X.carrier) (_ : y ∈ V)
        (j : V ⟶ (immOpensFunctor f).obj W), M.val.map j.op s = 0 := by
  constructor
  · rintro h y ⟨x, hxW, rfl⟩ hyZ
    obtain ⟨W₀, hxW₀, j, hj⟩ := h x hxW hyZ
    exact ⟨(immOpensFunctor f).obj W₀, ⟨x, hxW₀, rfl⟩, (immOpensFunctor f).map j, hj⟩
  · intro h x hxW hxZ
    obtain ⟨V, hV, jV, hjV⟩ := h (f.hom.base x) ⟨x, hxW, rfl⟩ hxZ
    refine ⟨(Opens.map f.hom.base).obj V ⊓ W, ⟨hV, hxW⟩, homOfLE inf_le_right, ?_⟩
    have hle : (immOpensFunctor f).obj ((Opens.map f.hom.base).obj V ⊓ W) ≤ V := by
      rintro z ⟨w, hw, rfl⟩
      exact hw.1
    change M.val.map ((immOpensFunctor f).map (homOfLE inf_le_right)).op s = 0
    exact map_eq_zero_of_eq_comp M _ jV.op (homOfLE hle).op
      (congrArg Quiver.Hom.op (Subsingleton.elim _ _)) s hjV

/-! ### The comparison at a module -/

/-- **The subsheaf of sections supported on `Z` restricts, along an open immersion, to the
subsheaf of sections supported on the preimage of `Z`.**  The comparison is compatible with the
two inclusions into the restriction of the coefficient module.

No closedness assumption on `Z` is used. -/
theorem exists_supportedSectionsImmRestrictIso
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ∃ e : (immRestrict f).obj (supportedSectionsSheaf Z M).1 ≅
        (supportedSectionsSheaf (⇑f.hom.base ⁻¹' Z) ((immRestrict f).obj M)).1,
      e.hom ≫ supportedSectionsSheafι (⇑f.hom.base ⁻¹' Z) ((immRestrict f).obj M) =
        (immRestrict f).map (supportedSectionsSheafι Z M) := by
  refine exists_iso_of_injective_same_range _ _ (fun V => ?_) (fun V => ?_) (fun V => ?_)
  · exact (supportedSectionsSheaf Z M).2.2.1 (op ((immOpensFunctor f).obj (unop V)))
  · exact (supportedSectionsSheaf (⇑f.hom.base ⁻¹' Z) ((immRestrict f).obj M)).2.2.1 V
  · ext s
    refine Iff.trans (mem_supportedSectionsSheafι_range_iff Z M
      (op ((immOpensFunctor f).obj (unop V))) s) ?_
    refine Iff.trans ?_ (mem_supportedSectionsSheafι_range_iff (⇑f.hom.base ⁻¹' Z)
      ((immRestrict f).obj M) V s).symm
    refine Iff.trans (suppSection_subset_iff_locally_eq_zero Z M
      ((immOpensFunctor f).obj (unop V)) s) ?_
    refine Iff.trans ?_ (suppSection_subset_iff_locally_eq_zero (⇑f.hom.base ⁻¹' Z)
      ((immRestrict f).obj M) (unop V) s).symm
    exact (locallyEqZero_immRestrict_iff f Z M (unop V) s).symm

/-! ### The comparison as an isomorphism of functors -/

/-- The inclusions `H_Z(ℱ)|_{X'} ⟶ ℱ|_{X'}` of the restricted subsheaf of sections with
support, as a natural transformation. -/
def immRestrictedSupportedSectionsι :
    supportedSectionsFunctor X Z ⋙ immRestrict f ⟶ immRestrict f where
  app M := (immRestrict f).map (supportedSectionsSheafι Z M)
  naturality M N g :=
    (((immRestrict f).map_comp ((supportedSectionsFunctor X Z).map g)
            (supportedSectionsSheafι Z N)).symm.trans
        (congrArg (immRestrict f).map (supportedSectionsSheafι_naturality Z g))).trans
      ((immRestrict f).map_comp (supportedSectionsSheafι Z M) g)

/-- The inclusions `H_{Z'}(ℱ|_{X'}) ⟶ ℱ|_{X'}` of the subsheaf of sections with support in the
preimage of `Z`, as a natural transformation. -/
def immSupportedSectionsιRestricted :
    immRestrict f ⋙ supportedSectionsFunctor X' (⇑f.hom.base ⁻¹' Z) ⟶ immRestrict f where
  app M := supportedSectionsSheafι (⇑f.hom.base ⁻¹' Z) ((immRestrict f).obj M)
  naturality _ _ g :=
    supportedSectionsSheafι_naturality (⇑f.hom.base ⁻¹' Z) ((immRestrict f).map g)

/-- **Excision for the subsheaf of sections with support, along an open immersion of ringed
spaces, as an isomorphism of functors** — in the concrete restriction `immRestrict f`.

The comparison at a single module is `exists_supportedSectionsImmRestrictIso`; what is added
here is that it is natural, which holds because both sides sit inside the restriction of the
coefficient module compatibly with the comparison and the inclusion of the second is a
monomorphism. -/
def supportedSectionsImmRestrictNatIso :
    supportedSectionsFunctor X Z ⋙ immRestrict f ≅
      immRestrict f ⋙ supportedSectionsFunctor X' (⇑f.hom.base ⁻¹' Z) :=
  NatIso.ofComponents
    (fun M => (exists_supportedSectionsImmRestrictIso f Z M).choose)
    (natIsoOfMonoOver_naturality (immRestrictedSupportedSectionsι f Z)
      (immSupportedSectionsιRestricted f Z)
      (fun _ => supportedSectionsSheafι_mono (⇑f.hom.base ⁻¹' Z) _)
      (fun M => (exists_supportedSectionsImmRestrictIso f Z M).choose)
      (fun M => (exists_supportedSectionsImmRestrictIso f Z M).choose_spec))

/-- **Excision for the subsheaf of sections with support, along an open immersion of ringed
spaces**:

`f^*(H_Z ℱ) ≅ H_{f^{-1}(Z)}(f^* ℱ)`,

naturally in the `𝒪_X`-module `ℱ`.  No closedness assumption on `Z` is used.

This is `supportedSectionsImmRestrictNatIso` conjugated by
`Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback`, which identifies the concrete
restriction along `f` with the abstract pullback `f^*`. -/
def supportedSectionsPullbackNatIso :
    supportedSectionsFunctor X Z ⋙ modulePullback f ≅
      modulePullback f ⋙ supportedSectionsFunctor X' (⇑f.hom.base ⁻¹' Z) :=
  Functor.isoWhiskerLeft (supportedSectionsFunctor X Z) (immRestrictIsoPullback f).symm ≪≫
    supportedSectionsImmRestrictNatIso f Z ≪≫
    Functor.isoWhiskerRight (immRestrictIsoPullback f)
      (supportedSectionsFunctor X' (⇑f.hom.base ⁻¹' Z))

end

end Stacks.SheafOfModules.SupportedSections

end
