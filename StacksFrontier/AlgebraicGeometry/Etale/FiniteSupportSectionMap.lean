module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSectionsClopen

/-!
# Maps of finite-support sections from restriction-compatible maps of sections

A map of the groups `H_Z(F)` of sections supported on a locally closed subset `Z` cannot be
built from a bare additive map on sections: it has to carry the support condition across, and
the support condition is not preserved by an arbitrary additive map. What does preserve it is
compatibility with restriction. If an additive map on the sections over an open `U` containing
`Z` as a closed subset agrees, after restriction to the part of `U` off `Z`, with an additive
map there, then a section supported on `Z` is sent to a section supported on `Z`, because being
supported on `Z` says exactly that the restriction off `Z` vanishes.

This file isolates that observation, and runs it through the colimit defining the group of
sections with finite support. The input is a family of additive maps on the sections over the
Zariski opens of a fixed object `W` of the small étale site, compatible with restriction along
the inclusions of those opens — the data an
`AlgebraicGeometry.SmallEtale.OpenSectionMap`. Such a family is *not* a morphism of abelian
sheaves on the small étale site: it is only defined over the opens of `W`, and it is naturality
over those alone that the argument needs. That is the regime of the construction which, for a
section `t` of a sheaf on the target, sends a section `s` of `F` to `s ⊗ t`: the family is
natural over the opens of the base change `X_V`, and over nothing larger.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OpenSectionMap` — the input data: additive maps on the sections
  over the Zariski opens of `W`, compatible with the restrictions between them.
* `AlgebraicGeometry.SmallEtale.OpenSectionMap.supportedSectionsHom` — the induced map of the
  groups `H_Z(F) ⟶ H_Z(G)` of sections supported on a locally closed subset.
* `AlgebraicGeometry.SmallEtale.OpenSectionMap.finiteSupportDiagramHom` and
  `AlgebraicGeometry.SmallEtale.OpenSectionMap.finiteSupportSectionsHom` — the induced morphism
  of the diagrams of supported sections over the supports finite over a test object, and the
  induced map of the groups of sections with finite support over it.

## Main results

* `AlgebraicGeometry.SmallEtale.supportSection_subset_of_restrict_comm` — the observation
  above: an additive map compatible with restriction along an open immersion whose image is the
  complement of `Z` does not enlarge a support past `Z`.
* `AlgebraicGeometry.SmallEtale.range_openObjectHomOfLE_supportOpenOffSupport` — the open
  immersion that observation is applied to: the canonical open of `Z` with `Z` removed has
  image the complement of `Z` inside the canonical open.
* `AlgebraicGeometry.SmallEtale.OpenSectionMap.supportedSectionsHom_naturality` — the induced
  maps commute with the transition maps of the colimit, which is what makes the map on
  finite-support sections well defined.
* `AlgebraicGeometry.SmallEtale.OpenSectionMap.finiteSupportSectionsHom_ι` — the effect of that
  map on a colimit generator: the pair `(Z, s)` goes to the pair `(Z, θ s)`, with the same
  support.

## Implementation notes

The complement of `Z` inside its canonical open `coborder Z` is realized as the Zariski open
`coborder Z \ closure Z` of the ambient object, not as `coborder Z \ Z`: the latter is the same
subset, by `coborder_inter_closure`, but only the former is visibly open. Removing a closed
subset from the canonical open is already available as
`AlgebraicGeometry.SmallEtale.supportOpenSdiff`, and the identification of the two subsets is
`AlgebraicGeometry.SmallEtale.supportOpenOffSupport_preimage`.

Naturality of an `AlgebraicGeometry.SmallEtale.OpenSectionMap` is required for every inclusion
of opens of `W`, not only for the one inclusion the support argument uses, because the
transition maps of the colimit `colim_Z H_Z(F)` are restrictions along the inclusions of the
canonical opens of the supports, and compatibility with those is what
`AlgebraicGeometry.SmallEtale.OpenSectionMap.supportedSectionsHom_naturality` needs.

What is *not* done here is naturality in the test object: an
`AlgebraicGeometry.SmallEtale.OpenSectionMap` lives over one object `W`, so this yields a map
of the groups of finite-support sections over one test object, not a morphism of the
finite-support direct image presheaves. Supplying that requires in addition a comparison of the
families over `V` and over `V'` for an arrow `V' ⟶ V`, matched against
`AlgebraicGeometry.SmallEtale.finiteSupportBaseChange`.

## References

* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

section SupportTransport

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- An additive map on sections which, after restriction along an open immersion whose image is
the complement of `Z`, agrees with an additive map there, does not enlarge a support past `Z`.
Being supported on `Z` says that the restriction to the complement vanishes, and that is
carried across by the compatibility. -/
public theorem supportSection_subset_of_restrict_comm
    {W' W : SmallEtale B S hS} (i : W' ⟶ W)
    [IsOpenImmersion ((SmallEtale.toScheme B S hS).map i)]
    (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (hRange : Set.range ((SmallEtale.toScheme B S hS).map i).base = Zᶜ)
    (θ : F.obj.obj (op W) →+ G.obj.obj (op W))
    (θ' : F.obj.obj (op W') →+ G.obj.obj (op W'))
    (hcomm : ∀ s, θ' (F.obj.map i.op s) = G.obj.map i.op (θ s))
    {s : F.obj.obj (op W)} (hs : supportSection B S hS F W s ⊆ Z) :
    supportSection B S hS G W (θ s) ⊆ Z := by
  rw [supportSection_subset_iff_zero_on_open B S hS F i Z hRange] at hs
  rw [supportSection_subset_iff_zero_on_open B S hS G i Z hRange, ← hcomm, hs, map_zero]

variable {S hS}

/-- The canonical open of a locally closed subset with the subset itself removed, as a Zariski
open of the ambient object: the closure of the subset is what is removed, which is the same
subset and visibly open. -/
public def supportOpenOffSupport (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z) :
    ((SmallEtale.toScheme B S hS).obj W).Opens :=
  supportOpenSdiff B S hS W hZ (isClosed_closure (s := Z))

/-- The canonical open with the support removed is contained in the canonical open. -/
public theorem supportOpenOffSupport_le (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z) :
    supportOpenOffSupport B W hZ ≤ supportOpen B S hS W Z hZ :=
  supportOpenSdiff_le B S hS W hZ _

/-- Inside the canonical open of a locally closed subset, removing the closure of the subset is
removing the subset. -/
public theorem supportOpenOffSupport_preimage (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z) :
    (supportOpen B S hS W Z hZ).ι.base ⁻¹'
        (supportOpenOffSupport B W hZ : Set ((SmallEtale.toScheme B S hS).obj W)) =
      ((supportOpen B S hS W Z hZ).ι.base ⁻¹' Z)ᶜ := by
  ext z
  have hz : z.1 ∈ coborder Z := z.2
  change z.1 ∈ (supportOpen B S hS W Z hZ : Set _) \ closure Z ↔ z.1 ∉ Z
  rw [Set.mem_sdiff]
  exact ⟨fun hzmem hzZ => hzmem.2 (subset_closure hzZ),
    fun hzZ => ⟨hz, fun hc => hzZ (mem_coborder_iff_imp.1 hz hc)⟩⟩

/-- The inclusion of the canonical open with the support removed has image the complement of
the support inside the canonical open. This is the open immersion
`AlgebraicGeometry.SmallEtale.supportSection_subset_of_restrict_comm` is applied to. -/
public theorem range_openObjectHomOfLE_supportOpenOffSupport (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z) :
    Set.range ((SmallEtale.toScheme B S hS).map
        (openObjectHomOfLE B S hS W (supportOpenOffSupport_le B W hZ))).base =
      ((supportOpen B S hS W Z hZ).ι.base ⁻¹' Z)ᶜ := by
  have h := opensRange_openObjectHomOfLE B S hS W (supportOpenOffSupport_le B W hZ)
  have h' := congrArg (fun U : ((SmallEtale.toScheme B S hS).obj
    (openObject B S hS W (supportOpen B S hS W Z hZ))).Opens =>
      (U : Set ((SmallEtale.toScheme B S hS).obj
        (openObject B S hS W (supportOpen B S hS W Z hZ))))) h
  exact h'.trans (supportOpenOffSupport_preimage B W hZ)

end SupportTransport

section OpenSectionMap

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
  (F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- Additive maps on the sections of `F` over the Zariski opens of a fixed object `W` of the
small étale site, compatible with restriction along the inclusions between those opens. This is
weaker than a morphism of abelian sheaves on the small étale site, which would be natural for
every arrow of the site; naturality over the opens of `W` alone is what the transport of
supports and the transition maps of the finite-support colimit consume. -/
public structure OpenSectionMap (W : SmallEtale B S hS) where
  /-- The additive map on the sections over each Zariski open of `W`. -/
  app : ∀ U : ((SmallEtale.toScheme B S hS).obj W).Opens,
    F.obj.obj (op (openObject B S hS W U)) →+ G.obj.obj (op (openObject B S hS W U))
  /-- Compatibility with restriction along the inclusion of one Zariski open in another. -/
  naturality : ∀ {U U' : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : U' ≤ U)
      (s : F.obj.obj (op (openObject B S hS W U))),
    app U' (F.obj.map (openObjectHomOfLE B S hS W h).op s) =
      G.obj.map (openObjectHomOfLE B S hS W h).op (app U s)

namespace OpenSectionMap

variable {B F G} {W : SmallEtale B S hS} (θ : OpenSectionMap B F G W)

/-- The induced map of the groups of sections supported on a locally closed subset. -/
public def supportedSectionsHom (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) :
    supportedSections B S hS F W Z hZ →+ supportedSections B S hS G W Z hZ where
  toFun s := ⟨θ.app (supportOpen B S hS W Z hZ) s.val,
    supportSection_subset_of_restrict_comm B S hS F G
      (openObjectHomOfLE B S hS W (supportOpenOffSupport_le B W hZ)) _
      (range_openObjectHomOfLE_supportOpenOffSupport B W hZ)
      (θ.app (supportOpen B S hS W Z hZ)) (θ.app (supportOpenOffSupport B W hZ))
      (θ.naturality (supportOpenOffSupport_le B W hZ)) s.property⟩
  map_zero' := Subtype.ext (θ.app (supportOpen B S hS W Z hZ)).map_zero
  map_add' s t := Subtype.ext ((θ.app (supportOpen B S hS W Z hZ)).map_add s.val t.val)

/-- The induced map on supported sections is `θ` on the underlying sections over the support
open. -/
@[simp]
public theorem supportedSectionsHom_val (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (s : supportedSections B S hS F W Z hZ) :
    (θ.supportedSectionsHom Z hZ s).val = θ.app (supportOpen B S hS W Z hZ) s.val :=
  rfl

/-- The induced maps commute with the transition maps of the colimit: enlarging the support and
then applying the family is applying the family and then enlarging the support. -/
public theorem supportedSectionsHom_naturality
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z)) :
    (θ.supportedSectionsHom Z' hZ').comp
        (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc) =
      (supportedSectionsMap B S hS G W Z Z' hZ hZ' h hc).comp
        (θ.supportedSectionsHom Z hZ) := by
  refine AddMonoidHom.ext fun s => Subtype.ext ?_
  rw [AddMonoidHom.coe_comp, Function.comp_apply, supportedSectionsHom_val,
    supportedSectionsMap_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    supportedSectionsMap_apply, supportedSectionsHom_val]
  exact θ.naturality (supportOpen_antitone B S hS W Z Z' hZ hZ' h hc) s.val

end OpenSectionMap

end OpenSectionMap

section FiniteSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}}
  {V : SmallEtale B Y.obj Y.property}

namespace OpenSectionMap

/-- The induced morphism of the diagrams `Z ↦ H_Z(F)` of supported sections over the supports
finite over a test object. -/
public def finiteSupportDiagramHom (θ : OpenSectionMap B F G (baseChange B f V)) :
    finiteSupportDiagram B f F V ⟶ finiteSupportDiagram B f G V where
  app E := AddCommGrpCat.ofHom
    (θ.supportedSectionsHom E.1 (finiteSupport_isLocallyClosed B f V E))
  naturality E E' k := AddCommGrpCat.hom_ext <|
    θ.supportedSectionsHom_naturality E.1 E'.1
      (finiteSupport_isLocallyClosed B f V E) (finiteSupport_isLocallyClosed B f V E')
      (leOfHom k) (finiteSupport_closedWithin B f V E E' (leOfHom k))

/-- The induced map of the groups of sections with finite support over a test object. -/
public def finiteSupportSectionsHom (θ : OpenSectionMap B F G (baseChange B f V))
    [Small.{v} (FiniteSupport B f V)] :
    finiteSupportSections B f F V ⟶ finiteSupportSections B f G V :=
  colim.map (θ.finiteSupportDiagramHom B f)

/-- The induced map sends the colimit generator of a support to the colimit generator of the
same support: the pair `(Z, s)` goes to the pair `(Z, θ s)`. -/
public theorem finiteSupportSectionsHom_ι (θ : OpenSectionMap B F G (baseChange B f V))
    [Small.{v} (FiniteSupport B f V)] (E : FiniteSupport B f V) :
    colimit.ι (finiteSupportDiagram B f F V) E ≫ θ.finiteSupportSectionsHom B f =
      AddCommGrpCat.ofHom
          (θ.supportedSectionsHom E.1 (finiteSupport_isLocallyClosed B f V E)) ≫
        colimit.ι (finiteSupportDiagram B f G V) E :=
  colimit.ι_map (θ.finiteSupportDiagramHom B f) E

end OpenSectionMap

end FiniteSupport

end AlgebraicGeometry.SmallEtale

end
