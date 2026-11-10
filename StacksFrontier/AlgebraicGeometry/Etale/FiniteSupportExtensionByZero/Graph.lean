module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The graph of an étale object and the section supported on it

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, and
let `F` be an abelian sheaf on the small étale site of `U`. This file sets up the
finite-support direct image presheaf `f_{p!}F = colim_Z H_Z(F)` of Stacks 0F6M for `j`, and the
geometric input of the canonical map `j_{p!}F ⟶ f_{p!}F` of Stacks 0F6Q from the presheaf
extension by zero: a section of `F` over an étale object `W → U` is sent to the generator of the
colimit `colim_Z H_Z(F)` at the graph of `W → U`. The graph is a morphism `W ⟶ U ×_X W` whose
first projection is the identity, hence an open immersion whose image is finite — indeed
isomorphic — over `W`; so its image is one of the supports indexing the colimit, and the
section, transported along the isomorphism of `W` with its graph, is a section of `F` supported
there. This file constructs that graph, its support and the supported section, and shows that
the supported section is natural in `F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleFiniteSupportPresheaf` — the finite-support direct image
  presheaf `f_{p!}` of Stacks 0F6M for the étale morphism `U ⟶ X`.
* `AlgebraicGeometry.SmallEtale.etaleGraphMap`,
  `AlgebraicGeometry.SmallEtale.etaleGraphFiniteSupport` and
  `AlgebraicGeometry.SmallEtale.etaleGraphSection` — the graph of an étale object over `U`
  inside its base change, the support it provides, and the supported section a section of `F`
  becomes on it.
* `AlgebraicGeometry.SmallEtale.etaleGraphIntoSupportOpen` — the factorization of the graph
  through the canonical open of its support.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleGraphSection_restrict` — restriction along the factorized
  graph recovers the section a graph-supported section was built from.
* `AlgebraicGeometry.SmallEtale.etaleGraphSection_ext` — a section supported on the graph is
  determined by that restriction.
* `AlgebraicGeometry.SmallEtale.etaleGraphSection_naturality` — the graph-supported section is
  natural in the abelian sheaf.

## Implementation notes

### The coefficient universe

Everything here happens at the single coefficient universe `AddCommGrpCat.{u + 1}` for the
scheme universe `u`, rather than at the universe `max (u + 1) v` at which
`AlgebraicGeometry.SmallEtale.finiteSupportPushforward` is available. That is forced from both
ends and is not a restriction of the mathematics: extension by zero
`AlgebraicGeometry.abelianExtensionByZero` and the whole stalk development of Stacks 03S5 are
stated at `u + 1`, and so is the criterion
`AlgebraicGeometry.isIso_of_isIso_etaleStalkMap` by which the sheafified map is shown to be an
isomorphism — the points of the small étale site live relative to `Type u`, and the germ
calculus delivers an isomorphism of sheaves only when the coefficient universe is `u + 1`.
Instantiating the finite-support side at `max u v = u + 1` costs nothing, since the supports
indexing the colimit are already small at `u + 1`.

### The graph and its two opens

A section of `F` supported on a locally closed `Z` is, by Stacks 0F6F, a section over the
canonical open `coborder Z`. For the graph of `W → U` the support `Z` is itself open, but
`coborder Z` is strictly larger in general, so two opens occur: the image of the graph, on
which the section is literally the transport of the given one along
`AlgebraicGeometry.SmallEtale.etaleGraphOpenIso`, and the canonical open
`AlgebraicGeometry.SmallEtale.finiteSupportOpen`, on which the supported section lives. The
identification of sections over the two is
`AlgebraicGeometry.SmallEtale.supportedSectionsOpenEquiv`, and
`AlgebraicGeometry.SmallEtale.etaleGraphIntoSupportOpen` is the resulting factorization of the
graph through the canonical open; restriction along it recovers the original section, which is
what pins the construction down.

## References

* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-! ### The finite-support direct image of an étale morphism -/

/-- The structure morphism of an object of the small étale site is locally quasi-finite,
being étale. This is what makes the finite-support direct image of Stacks 0F6M available
for it. -/
public instance locallyQuasiFinite_smallEtale_hom (W : SmallEtale B X hX) :
    LocallyQuasiFinite (B.inclusion.map W.obj.hom) :=
  (locallyQuasiFinite_of_etale (B.inclusion.map W.obj.hom)).2

/-- The supports finite over an étale test object are small at the coefficient universe, so
the colimit of Stacks 0F6M defining the finite-support direct image exists. -/
public theorem small_finiteSupport_smallEtale :
    ∀ V : SmallEtale B X hX, Small.{u + 1} (FiniteSupport B U.obj.hom V) :=
  fun _ => inferInstance

/-- The finite-support direct image presheaf of Stacks 0F6M, together with its
characterisation, for the étale morphism `U ⟶ X`. -/
public abbrev etaleFiniteSupportData :=
  finiteSupportPushforward B U.obj.hom (small_finiteSupport_smallEtale B X hX U)

/-- **Stacks 0F6M** for an étale morphism: the presheaf `f_{p!}F = colim_Z H_Z(F)` on the
small étale site of `X`, functorially in the abelian sheaf `F` on the small étale site
of `U`. -/
public abbrev etaleFiniteSupportPresheaf :
    Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1} ⥤
      ((SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (etaleFiniteSupportData B X hX U).1

/-! ### The graph of an étale object over `U` -/

/-- The graph of an étale object `W → U`: the morphism `W ⟶ U ×_X W` with components the
morphism `W ⟶ U` and the identity of `W`. -/
public def etaleGraphMap (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    W.obj.left ⟶
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)).obj.left :=
  pullback.lift (𝟙 W.obj.left) W.obj.hom (by
    change 𝟙 _ ≫ ((smallEtalePostcompose B X hX U).obj W).obj.hom = W.obj.hom ≫ U.obj.hom
    simp [smallEtalePostcompose])

/-- The first projection of the graph of `W → U` is the identity of `W`. -/
@[simp] public theorem etaleGraphMap_fst
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    etaleGraphMap B X hX U W ≫
        pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph of `W → U` is the structure morphism `W ⟶ U`. -/
@[simp] public theorem etaleGraphMap_snd
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    etaleGraphMap B X hX U W ≫
        pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom =
      W.obj.hom :=
  pullback.lift_snd _ _ _

/-- The first projection of the graph of `W → U` is the identity of `W`, as morphisms of
schemes. -/
public theorem etaleGraphMap_comp_fst
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    B.inclusion.map (etaleGraphMap B X hX U W) ≫ B.inclusion.map
        (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) = 𝟙 _ :=
  congrArg B.inclusion.map (etaleGraphMap_fst B X hX U W)

/-- The second projection of the graph of `W → U` is the structure morphism `W ⟶ U`, as
morphisms of schemes. -/
public theorem etaleGraphMap_comp_snd
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    B.inclusion.map (etaleGraphMap B X hX U W) ≫ B.inclusion.map
        (pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
      B.inclusion.map W.obj.hom :=
  congrArg B.inclusion.map (etaleGraphMap_snd B X hX U W)

/-- The graph of an étale object over `U` is an open immersion: it is a section of the first
projection of `U ×_X W ⟶ W`, which is étale, and an étale morphism admitting a retraction is
an open immersion because an étale morphism has an open diagonal. -/
public theorem etaleGraphMap_isOpenImmersion
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsOpenImmersion (B.inclusion.map (etaleGraphMap B X hX U W)) := by
  have hdiag : @Etale ≤ (@IsOpenImmersion : MorphismProperty Scheme).diagonal := by
    intro A C g hg
    change IsOpenImmersion (pullback.diagonal g)
    have : Etale g := hg
    infer_instance
  have : IsOpenImmersion.HasOfPostcompProperty (@Etale) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 hdiag
  have hsq := ((IsPullback.of_hasPullback
    ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom).flip).map B.inclusion
  have hfst : Etale (B.inclusion.map
      (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  refine MorphismProperty.of_postcomp (W := IsOpenImmersion) (W' := @Etale)
    (B.inclusion.map (etaleGraphMap B X hX U W))
    (B.inclusion.map
      (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom)) hfst ?_
  change IsOpenImmersion (B.inclusion.map (etaleGraphMap B X hX U W ≫
    pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom))
  rw [etaleGraphMap_fst]
  exact MorphismProperty.id_mem IsOpenImmersion _

/-- The graph of `W → U` is an open immersion. -/
public instance isOpenImmersion_etaleGraphMap
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsOpenImmersion (B.inclusion.map (etaleGraphMap B X hX U W)) :=
  etaleGraphMap_isOpenImmersion B X hX U W

/-- The graph of `W → U`, as a morphism `W ⟶ U ×_X W` of the small étale site of `U`. -/
public def etaleGraph (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    W ⟶ baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W) :=
  ObjectProperty.homMk (Over.homMk (etaleGraphMap B X hX U W)
    (by exact etaleGraphMap_snd B X hX U W))

/-- The underlying morphism of schemes of the graph of `W → U` is the graph. -/
@[simp] public theorem etaleGraph_toScheme_map
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map (etaleGraph B X hX U W) =
      B.inclusion.map (etaleGraphMap B X hX U W) :=
  rfl

/-- The image of the graph of `W → U` is a support finite over `W`: the graph is an open
immersion, and composed with the first projection it is the identity of `W`, hence finite. -/
public def etaleGraphFiniteSupport (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    FiniteSupport B U.obj.hom ((smallEtalePostcompose B X hX U).obj W) :=
  ⟨Set.range (B.inclusion.map (etaleGraphMap B X hX U W)).base,
    ⟨B.inclusion.obj W.obj.left, B.inclusion.map (etaleGraphMap B X hX U W), inferInstance,
      by
        have hg : B.inclusion.map (etaleGraphMap B X hX U W) ≫ B.inclusion.map
            (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
            𝟙 (B.inclusion.obj W.obj.left) :=
          etaleGraphMap_comp_fst B X hX U W
        rw [hg]
        exact MorphismProperty.id_mem (@IsFinite) _,
      rfl⟩⟩

/-- The support carried by the graph of `W → U` is the image of the graph. -/
public theorem etaleGraphFiniteSupport_coe
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (etaleGraphFiniteSupport B X hX U W).1 =
      Set.range (B.inclusion.map (etaleGraphMap B X hX U W)).base :=
  rfl

/-- The image of the graph of `W → U`, as an open of the base change `U ×_X W`. -/
public def etaleGraphOpen (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))).Opens :=
  (B.inclusion.map (etaleGraphMap B X hX U W)).opensRange

/-- The open image of the graph of `W → U` is the support it carries. -/
public theorem etaleGraphOpen_coe (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    ((etaleGraphOpen B X hX U W : Set _)) = (etaleGraphFiniteSupport B X hX U W).1 :=
  rfl

/-- Inside the open image of the graph of `W → U` the support carried by the graph is
everything. -/
public theorem etaleGraphOpen_preimage_support
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (etaleGraphOpen B X hX U W).ι.base ⁻¹' (etaleGraphFiniteSupport B X hX U W).1 =
      Set.univ := by
  rw [← etaleGraphOpen_coe, Set.preimage_eq_univ_iff, Scheme.Opens.range_ι]

/-- The support carried by the graph of `W → U` is closed in the open image of the graph:
there it is everything. -/
public theorem etaleGraphOpen_isClosed_preimage
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsClosed ((etaleGraphOpen B X hX U W).ι.base ⁻¹'
      (etaleGraphFiniteSupport B X hX U W).1) :=
  etaleGraphOpen_preimage_support B X hX U W ▸ isClosed_univ

/-- The support carried by the graph of `W → U` is contained in the open image of the
graph. -/
public theorem etaleGraphFiniteSupport_subset_graphOpen
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (etaleGraphFiniteSupport B X hX U W).1 ⊆
      (etaleGraphOpen B X hX U W : Set _) :=
  (etaleGraphOpen_coe B X hX U W).ge

/-- The graph identifies `W` with the open of `U ×_X W` which is its image, as objects of the
small étale site of `U`. -/
public def etaleGraphOpenIsoData (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    {e : W ≅ openObject B U.obj.left.1 U.obj.left.property
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphOpen B X hX U W) //
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map e.hom ≫
        (etaleGraphOpen B X hX U W).ι =
        B.inclusion.map (etaleGraphMap B X hX U W)} := by
  let O := etaleGraphOpen B X hX U W
  have hsubset : Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraph B X hX U W)).base ⊆ O := by
    rw [etaleGraph_toScheme_map]
    exact le_refl _
  let m := factorThroughOpenObject B U.obj.left.1 U.obj.left.property W
    (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
    (etaleGraph B X hX U W) O hsubset
  have hfac := factorThroughOpenObject_fac B U.obj.left.1 U.obj.left.property W
    (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
    (etaleGraph B X hX U W) O hsubset
  have hms : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map m ≫ O.ι =
      B.inclusion.map (etaleGraphMap B X hX U W) := by
    have h := congrArg (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map hfac
    rwa [Functor.map_comp, openObjectι_map, etaleGraph_toScheme_map] at h
  have hopen : IsOpenImmersion
      ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map m) := by
    have hcomp : IsOpenImmersion
        ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map m ≫ O.ι) := by
      rw [hms]
      infer_instance
    exact IsOpenImmersion.of_comp _ O.ι
  have hiso : IsIso ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map m) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    refine top_unique fun x _ => ?_
    obtain ⟨y, hy⟩ : ∃ y, (B.inclusion.map (etaleGraphMap B X hX U W)).base y = x.1 := x.2
    exact ⟨y, Subtype.ext ((congrArg (fun k : Scheme.Hom _ _ => k.base y) hms).trans hy)⟩
  have : IsIso (B.inclusion.map m.hom.left) := hiso
  have : IsIso m.hom.left := isIso_of_fully_faithful B.inclusion m.hom.left
  exact ⟨(BigEtaleOver.IsEtaleOver B U.obj.left.1 U.obj.left.property).isoMk
    (Over.isoMk (asIso m.hom.left) (Over.w m.hom)), hms⟩

/-- The isomorphism of `W` with the open image of its graph in `U ×_X W`. -/
public abbrev etaleGraphOpenIso (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    W ≅ openObject B U.obj.left.1 U.obj.left.property
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphOpen B X hX U W) :=
  (etaleGraphOpenIsoData B X hX U W).1

/-- The isomorphism of `W` with the open image of its graph is the graph. -/
public theorem etaleGraphOpenIso_hom_ι
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (etaleGraphOpenIso B X hX U W).hom ≫ (etaleGraphOpen B X hX U W).ι =
      B.inclusion.map (etaleGraphMap B X hX U W) :=
  (etaleGraphOpenIsoData B X hX U W).2

/-! ### The section supported on the graph -/

/-- The open image of the graph of `W → U` is contained in the canonical open of the support
it carries. -/
public theorem etaleGraphOpen_le_finiteSupportOpen
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    etaleGraphOpen B X hX U W ≤
      finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
        (etaleGraphFiniteSupport B X hX U W) := by
  intro x hx
  exact subset_supportOpen B U.obj.left.1 U.obj.left.property _ _ _
    (etaleGraphOpen_coe B X hX U W ▸ hx)

section GraphSection

variable (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
  AddCommGrpCat.{u + 1})

/-- A section of `F` over `W`, read on the open image of the graph of `W → U` through the
identification of `W` with that image. It is supported on the graph because the graph is all
of that open. -/
public def etaleGraphSectionOnOpen (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) →+ supportedSectionsOnOpen B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1 (etaleGraphOpen B X hX U W) where
  toFun s := ⟨F.obj.map (etaleGraphOpenIso B X hX U W).inv.op s, by
    rw [etaleGraphOpen_preimage_support]
    exact Set.subset_univ _⟩
  map_zero' := Subtype.ext (F.obj.map (etaleGraphOpenIso B X hX U W).inv.op).hom.map_zero
  map_add' a b := Subtype.ext (map_add _ _ _)

/-- **The graph-supported section.** A section of `F` over an étale object `W → U` becomes a
section of `F` supported on the graph of `W → U` inside `U ×_X W`. -/
public def etaleGraphSection (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) →+ supportedSections B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W)) :=
  (supportedSectionsOpenEquiv B U.obj.left.1 U.obj.left.property F
    (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
    (etaleGraphFiniteSupport B X hX U W).1
    (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
    (etaleGraphOpen B X hX U W) (etaleGraphFiniteSupport_subset_graphOpen B X hX U W)
    (etaleGraphOpen_isClosed_preimage B X hX U W)).symm.toAddMonoidHom.comp
      (etaleGraphSectionOnOpen B X hX U F W)

/-- On the open image of the graph, the graph-supported section is the given section read
through the identification of `W` with that image. -/
public theorem etaleGraphSection_onOpen (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (s : F.obj.obj (op W)) :
    ((supportedSectionsOpenEquiv B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
      (etaleGraphOpen B X hX U W) (etaleGraphFiniteSupport_subset_graphOpen B X hX U W)
      (etaleGraphOpen_isClosed_preimage B X hX U W))
        (etaleGraphSection B X hX U F W s)).val =
      F.obj.map (etaleGraphOpenIso B X hX U W).inv.op s :=
  congrArg Subtype.val ((supportedSectionsOpenEquiv B U.obj.left.1 U.obj.left.property F
    (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
    (etaleGraphFiniteSupport B X hX U W).1
    (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
    (etaleGraphOpen B X hX U W) (etaleGraphFiniteSupport_subset_graphOpen B X hX U W)
    (etaleGraphOpen_isClosed_preimage B X hX U W)).apply_symm_apply
      (etaleGraphSectionOnOpen B X hX U F W s))

/-! ### The graph inside the canonical open of its support -/

/-- The factorization of the graph of `W → U` through the canonical open of the support it
carries: the identification of `W` with the open image of the graph, followed by the inclusion
of that open in the canonical one. -/
public def etaleGraphIntoSupportOpen
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    W ⟶ finiteSupportOpenObject B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
      (etaleGraphFiniteSupport B X hX U W) :=
  (etaleGraphOpenIso B X hX U W).hom ≫
    openObjectHomOfLE B U.obj.left.1 U.obj.left.property
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphOpen_le_finiteSupportOpen B X hX U W)

/-- Composed with the inclusion of the canonical open of its support, the factorized graph is
the graph. -/
public theorem etaleGraphIntoSupportOpen_comp
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (etaleGraphIntoSupportOpen B X hX U W) ≫
        (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).ι =
      B.inclusion.map (etaleGraphMap B X hX U W) := by
  rw [etaleGraphIntoSupportOpen, Functor.map_comp, Category.assoc,
    openObjectHomOfLE_map, Scheme.homOfLE_ι]
  exact etaleGraphOpenIso_hom_ι B X hX U W

/-- The factorized graph of `W → U` is an open immersion. -/
public theorem etaleGraphIntoSupportOpen_isOpenImmersion
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsOpenImmersion ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraphIntoSupportOpen B X hX U W)) := by
  rw [etaleGraphIntoSupportOpen, Functor.map_comp, openObjectHomOfLE_map]
  have : IsIso ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraphOpenIso B X hX U W).hom) :=
    ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).mapIso
      (etaleGraphOpenIso B X hX U W)).isIso_hom
  infer_instance

/-- The image of the factorized graph of `W → U` inside the canonical open of its support is
exactly that support. -/
public theorem etaleGraphIntoSupportOpen_range
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        (etaleGraphIntoSupportOpen B X hX U W)).base =
      (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
        (etaleGraphFiniteSupport B X hX U W)).ι.base ⁻¹'
          (etaleGraphFiniteSupport B X hX U W).1 := by
  have hcomp := etaleGraphIntoSupportOpen_comp B X hX U W
  have hbase (y : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W) :
      (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).ι.base
        (((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
          (etaleGraphIntoSupportOpen B X hX U W)).base y) =
        (B.inclusion.map (etaleGraphMap B X hX U W)).base y := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : Scheme.Hom _ _ => k.base y) hcomp
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, hbase]
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.val_injective ((hbase y).trans hy)⟩

/-- The factorized graph of `W → U` is a closed immersion onto the support inside the
canonical open: its image is the support, which is closed there. -/
public theorem etaleGraphIntoSupportOpen_isClosedImmersion
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsClosedImmersion ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      (etaleGraphIntoSupportOpen B X hX U W)) := by
  have := etaleGraphIntoSupportOpen_isOpenImmersion B X hX U W
  apply IsClosedImmersion.of_isPreimmersion
  exact (etaleGraphIntoSupportOpen_range B X hX U W).symm ▸
    isClosed_supportOpen_preimage B U.obj.left.1 U.obj.left.property _ _ _

/-- On the open image of the graph, a section supported on the graph is its own restriction
along the inclusion of that open in the canonical one. -/
public theorem etaleGraphSection_openEquiv_val
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (c : supportedSections B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))) :
    ((supportedSectionsOpenEquiv B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
      (etaleGraphOpen B X hX U W) (etaleGraphFiniteSupport_subset_graphOpen B X hX U W)
      (etaleGraphOpen_isClosed_preimage B X hX U W)) c).val =
    F.obj.map (openObjectHomOfLE B U.obj.left.1 U.obj.left.property
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphOpen_le_finiteSupportOpen B X hX U W)).op c.val :=
  locallyClosedSupportEquiv_restrict B U.obj.left.1 U.obj.left.property F _ _ _ _ _ _ _ _
    (etaleGraphOpen_le_finiteSupportOpen B X hX U W) c

/-- Restriction of a section supported on the graph along the factorized graph is its
restriction to the open image of the graph, read on `W`. -/
public theorem etaleGraphSection_restrict_eq
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (c : supportedSections B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))) :
    F.obj.map (etaleGraphIntoSupportOpen B X hX U W).op c.val =
      F.obj.map (etaleGraphOpenIso B X hX U W).hom.op
        (F.obj.map (openObjectHomOfLE B U.obj.left.1 U.obj.left.property
          (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
          (etaleGraphOpen_le_finiteSupportOpen B X hX U W)).op c.val) := by
  rw [etaleGraphIntoSupportOpen, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]

/-- Restriction along the factorized graph recovers the section a graph-supported section was
built from. This is what pins down the graph-supported section. -/
public theorem etaleGraphSection_restrict
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (s : F.obj.obj (op W)) :
    F.obj.map (etaleGraphIntoSupportOpen B X hX U W).op
      (etaleGraphSection B X hX U F W s).val = s := by
  have h : F.obj.map (openObjectHomOfLE B U.obj.left.1 U.obj.left.property
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphOpen_le_finiteSupportOpen B X hX U W)).op
        (etaleGraphSection B X hX U F W s).val =
      F.obj.map (etaleGraphOpenIso B X hX U W).inv.op s :=
    (etaleGraphSection_openEquiv_val B X hX U F W (etaleGraphSection B X hX U F W s)).symm.trans
      (etaleGraphSection_onOpen B X hX U F W s)
  rw [etaleGraphSection_restrict_eq, h, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
    ← op_comp, Iso.hom_inv_id, op_id, F.obj.map_id, ConcreteCategory.id_apply]

/-- A section supported on the graph of `W → U` is determined by its restriction along the
factorized graph. -/
public theorem etaleGraphSection_ext
    (W : SmallEtale B U.obj.left.1 U.obj.left.property)
    (a b : supportedSections B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W).1
      (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W)))
    (h : F.obj.map (etaleGraphIntoSupportOpen B X hX U W).op a.val =
      F.obj.map (etaleGraphIntoSupportOpen B X hX U W).op b.val) : a = b := by
  rw [etaleGraphSection_restrict_eq, etaleGraphSection_restrict_eq] at h
  have h' := (ConcreteCategory.bijective_of_isIso
    (F.obj.map (etaleGraphOpenIso B X hX U W).hom.op)).1 h
  refine (supportedSectionsOpenEquiv B U.obj.left.1 U.obj.left.property F
    (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
    (etaleGraphFiniteSupport B X hX U W).1
    (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
    (etaleGraphOpen B X hX U W) (etaleGraphFiniteSupport_subset_graphOpen B X hX U W)
    (etaleGraphOpen_isClosed_preimage B X hX U W)).injective (Subtype.ext ?_)
  rw [etaleGraphSection_openEquiv_val, etaleGraphSection_openEquiv_val]
  exact h'

end GraphSection

/-! ### Naturality of the graph-supported section in the abelian sheaf -/

/-- A morphism of abelian sheaves carries the section supported on the graph of `W → U`
determined by a section of the source to the one determined by its image. -/
public theorem etaleGraphSection_naturality
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (s : F.obj.obj (op W)) :
    supportedSectionsSheafMap B U.obj.left.1 U.obj.left.property φ
        (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
        (etaleGraphFiniteSupport B X hX U W).1
        (finiteSupport_isLocallyClosed B U.obj.hom _ (etaleGraphFiniteSupport B X hX U W))
        (etaleGraphSection B X hX U F W s) =
      etaleGraphSection B X hX U G W (φ.hom.app (op W) s) := by
  refine etaleGraphSection_ext B X hX U G W _ _ ?_
  rw [etaleGraphSection_restrict]
  change G.obj.map (etaleGraphIntoSupportOpen B X hX U W).op
    (φ.hom.app _ (etaleGraphSection B X hX U F W s).val) = _
  rw [← ConcreteCategory.comp_apply, ← φ.hom.naturality, ConcreteCategory.comp_apply,
    etaleGraphSection_restrict]

end AlgebraicGeometry.SmallEtale

end
