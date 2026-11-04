module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.Graph

/-!
# The canonical map from extension by zero to the finite-support direct image

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, and
let `F` be an abelian sheaf on the small étale site of `U`. This file constructs the canonical
map `j_{p!}F ⟶ f_{p!}F` of Stacks 0F6Q from the presheaf extension by zero `j_{p!}F`, the left
Kan extension `V ↦ ⨁_{φ : V → U} F(V →^φ U)` of Stacks 03S3, to the finite-support direct image
presheaf `f_{p!}F = colim_Z H_Z(F)` of Stacks 0F6M, natural in `F`.

The map comes from the universal property of the left Kan extension, so it is determined by
what it does on a section of `F` over an étale object `W → U`: such a section is sent to the
generator of the colimit `colim_Z H_Z(F)` at the graph of `W → U`, carrying the section
supported on that graph. For these graph generators to assemble into a map, they must be
compatible with restriction along a morphism `W' ⟶ W` of étale test objects; this is the
statement that the graph of `W' → U` is the base change of the graph of `W → U`, and that the
support it carries is the inverse image of the one carried by the graph of `W → U`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.graphSectionToFiniteSupport` — the graph generator of
  `colim_Z H_Z(F)` determined by a section of `F` over an étale object over `U`.
* `AlgebraicGeometry.SmallEtale.GraphSupportedSectionData` and
  `AlgebraicGeometry.SmallEtale.graphSupportedSection` — the graph, its support, the
  factorization of the graph through the canonical open of that support, and the supported
  section, bundled with the identities characterising them.
* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupport` — **Stacks 0F6Q**, the
  canonical natural map `j_{p!} ⟶ f_{p!}`.

## Main results

* `AlgebraicGeometry.SmallEtale.etaleGraph_naturality` and
  `AlgebraicGeometry.SmallEtale.etaleGraphFiniteSupport_baseChange` — the graph and its support
  are compatible with base change along a morphism of étale test objects.
* `AlgebraicGeometry.SmallEtale.etaleExtensionToFiniteSupport_on_graph` — the value of the
  canonical map on the generator of the left Kan extension coming from a section over an étale
  object `W → U` is the colimit generator at the graph of `W`.

## Implementation notes

### One spelling per object

The scheme underlying the base change `U ×_X W` has two names, the chosen fibre product
`pullback V.hom j` and the object `AlgebraicGeometry.SmallEtale.baseChange` of the small étale
site of `U`, which are interchangeable only at default transparency; the same happens for the
value of the finite-support direct image over an étale test object and the colimit
`colim_Z H_Z(F)`. A rewrite inside a goal mixing two such spellings fails, so each one is pinned
once: the private definitions of the base-change section fix the projections of the fibre
square with their source and target named in the small étale site, and
`AlgebraicGeometry.SmallEtale.graphDiagramSection` and
`AlgebraicGeometry.SmallEtale.graphSectionToFiniteSupport` state the comparison in the colimit
spelling. Everything else is written in one of those spellings throughout.

## References

* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-! ### Base change of the graph along a morphism of étale test objects -/

/-- Composition with the structure morphism of `U` does not change the underlying morphism of
schemes. -/
@[simp] public theorem smallEtalePostcompose_toScheme_map
    {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (g : W' ⟶ W) :
    (SmallEtale.toScheme B X hX).map ((smallEtalePostcompose B X hX U).map g) =
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g :=
  rfl

section BaseChange

variable {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (g : W' ⟶ W)

/-! The spellings of the morphisms of the fibre square `U ×_X W` are pinned here. The scheme
underlying the base change has two names, the chosen fibre product `pullback V.hom j` and the
object `baseChange B j V` of the small étale site of `U`, and they are interchangeable only at
default transparency; so the projections are given once with their source and target named in
the small étale site, and the identities they satisfy are restated for those spellings. Every
rewrite below then stays inside one vocabulary. -/

/-- The first projection `U ×_X W ⟶ W` of the base change of `U` along an étale object over
`U`, read as a morphism of the underlying schemes of objects of the small étale site. -/
private def graphFst (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)) ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W :=
  B.inclusion.map (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom)

/-- The second projection `U ×_X W ⟶ U` of the base change of `U` along an étale object
over `U`. -/
private def graphSnd (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)) ⟶
      B.inclusion.obj U.obj.left :=
  B.inclusion.map (pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom)

/-- The structure morphism `W ⟶ U` of an étale object over `U`. -/
private def graphStruct (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W ⟶
      B.inclusion.obj U.obj.left :=
  B.inclusion.map W.obj.hom

/-- The structure morphism `W ⟶ X` of an étale object over `U`, read through `U`. -/
private def graphBase (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W ⟶
      B.inclusion.obj (B.obj X hX) :=
  B.inclusion.map ((smallEtalePostcompose B X hX U).obj W).obj.hom

/-- The étale morphism `U ⟶ X`. -/
private def graphRoot : B.inclusion.obj U.obj.left ⟶ B.inclusion.obj (B.obj X hX) :=
  B.inclusion.map U.obj.hom

/-- The graph of `W → U` inside `U ×_X W`, with source and target named in the small étale
site of `U`. -/
private def graphHom (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W ⟶
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
        (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)) :=
  B.inclusion.map (etaleGraphMap B X hX U W)

/-- The base change `U ×_X W' ⟶ U ×_X W` of a morphism `W' ⟶ W` of étale objects over `U`. -/
private def graphBaseChange : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W')) ⟶
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)) :=
  (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
    ((smallEtaleBaseChange B U.obj.hom).map ((smallEtalePostcompose B X hX U).map g))

/-- `U ×_X W` is the fibre product of `W ⟶ X` and `U ⟶ X`. -/
private theorem isPullback_graphProj (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    IsPullback (graphFst B X hX U W) (graphSnd B X hX U W) (graphBase B X hX U W)
      (graphRoot B X hX U) :=
  (IsPullback.of_hasPullback ((smallEtalePostcompose B X hX U).obj W).obj.hom
    U.obj.hom).map B.inclusion

/-- The graph of `W → U` is a section of the first projection. -/
private theorem graphHom_fst (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    graphHom B X hX U W ≫ graphFst B X hX U W = 𝟙 _ :=
  etaleGraphMap_comp_fst B X hX U W

/-- The second projection of the graph of `W → U` is the structure morphism of `W`. -/
private theorem graphHom_snd (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    graphHom B X hX U W ≫ graphSnd B X hX U W = graphStruct B X hX U W :=
  etaleGraphMap_comp_snd B X hX U W

/-- Base change commutes with the first projection. -/
private theorem graphBaseChange_fst :
    graphBaseChange B X hX U g ≫ graphFst B X hX U W =
      graphFst B X hX U W' ≫
        (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g :=
  toScheme_baseChange_comp_fst B U.obj.hom _ _ ((smallEtalePostcompose B X hX U).map g)

/-- Base change commutes with the second projection. -/
private theorem graphBaseChange_snd :
    graphBaseChange B X hX U g ≫ graphSnd B X hX U W = graphSnd B X hX U W' :=
  SmallEtale.toScheme_map_comp B U.obj.left.1 U.obj.left.property
    ((smallEtaleBaseChange B U.obj.hom).map ((smallEtalePostcompose B X hX U).map g))

/-- A morphism of étale objects over `U` commutes with the structure morphisms to `U`. -/
private theorem toScheme_map_graphStruct :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g ≫
      graphStruct B X hX U W = graphStruct B X hX U W' :=
  SmallEtale.toScheme_map_comp B U.obj.left.1 U.obj.left.property g

/-- The graph is natural in the étale test object: the graph of `W' → U` followed by the base
change of `W' → W` is the graph of `W → U` preceded by `W' → W`. -/
private theorem graphHom_naturality :
    graphHom B X hX U W' ≫ graphBaseChange B X hX U g =
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g ≫
        graphHom B X hX U W := by
  refine (isPullback_graphProj B X hX U W).hom_ext ?_ ?_
  · simp only [Category.assoc, graphHom_fst, Category.comp_id]
    rw [graphBaseChange_fst, ← Category.assoc, graphHom_fst, Category.id_comp]
  · simp only [Category.assoc, graphBaseChange_snd, graphHom_snd, toScheme_map_graphStruct]

/-- A cone over the naturality square of the graph factors through `W'` by the first
projection, the factorization being compatible with the second leg of the cone. -/
private theorem graphCone_snd (c : PullbackCone (graphBaseChange B X hX U g)
    (graphHom B X hX U W)) :
    (c.fst ≫ graphFst B X hX U W') ≫
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g = c.snd := by
  rw [Category.assoc, ← graphBaseChange_fst, ← Category.assoc, c.condition, Category.assoc,
    graphHom_fst, Category.comp_id]

/-- The graph of `W' → U` is the base change of the graph of `W → U` along `W' → W`: the
square expressing naturality of the graph is a fibre square. -/
private theorem graphHom_isPullback :
    IsPullback (graphHom B X hX U W')
      ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g)
      (graphBaseChange B X hX U g) (graphHom B X hX U W) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (graphHom_naturality B X hX U g)
    (fun c => c.fst ≫ graphFst B X hX U W') (fun c => ?_) (graphCone_snd B X hX U g)
    (fun c m hm _ => ?_))
  · refine (isPullback_graphProj B X hX U W').hom_ext ?_ ?_
    · rw [Category.assoc, graphHom_fst, Category.comp_id]
    · rw [Category.assoc, graphHom_snd, ← toScheme_map_graphStruct, ← Category.assoc,
        graphCone_snd, ← graphHom_snd, ← Category.assoc, ← c.condition, Category.assoc,
        graphBaseChange_snd]
  · rw [← hm, Category.assoc, graphHom_fst, Category.comp_id]

/-- The graph is natural in the étale test object: the graph of `W' → U` followed by the base
change of `W' → W` is the graph of `W → U` preceded by `W' → W`. -/
public theorem etaleGraph_naturality :
    B.inclusion.map (etaleGraphMap B X hX U W') ≫
        (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
          ((smallEtaleBaseChange B U.obj.hom).map
            ((smallEtalePostcompose B X hX U).map g)) =
      (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g ≫
        B.inclusion.map (etaleGraphMap B X hX U W) :=
  graphHom_naturality B X hX U g

/-- The support carried by the graph of `W' → U` is the inverse image of the one carried by the
graph of `W → U`. This is what makes the comparison map compatible with restriction. -/
public theorem etaleGraphFiniteSupport_baseChange :
    (etaleGraphFiniteSupport B X hX U W').1 =
      ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
        ((smallEtaleBaseChange B U.obj.hom).map
          ((smallEtalePostcompose B X hX U).map g))).base ⁻¹'
        (etaleGraphFiniteSupport B X hX U W).1 := by
  have hnat := graphHom_naturality B X hX U g
  have hcoe : ∀ V : SmallEtale B U.obj.left.1 U.obj.left.property,
      (etaleGraphFiniteSupport B X hX U V).1 = Set.range (graphHom B X hX U V).base :=
    fun _ => rfl
  show (etaleGraphFiniteSupport B X hX U W').1 =
    (graphBaseChange B X hX U g).base ⁻¹' (etaleGraphFiniteSupport B X hX U W).1
  rw [hcoe, hcoe]
  refine Set.Subset.antisymm ?_ ?_
  · rintro p ⟨w, rfl⟩
    refine ⟨((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map g).base w, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using congr(($hnat).base w).symm
  · intro x hx
    have H := graphHom_isPullback B X hX U g
    let _ : IsOpenImmersion (graphHom B X hX U W) :=
      isOpenImmersion_etaleGraphMap B X hX U W
    obtain ⟨y, hy⟩ := (IsOpenImmersion.range_pullbackFst (graphHom B X hX U W)
      (graphBaseChange B X hX U g)).ge hx
    refine ⟨H.isoPullback.inv.base y, ?_⟩
    exact congr(($H.isoPullback_inv_fst).base y).trans hy

end BaseChange

/-! ### The canonical comparison map -/

section Comparison

variable (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
  AddCommGrpCat.{u + 1})

/-! The finite-support direct image is characterised rather than constructed, so the colimit
`colim_Z H_Z(F)` and its value over an étale test object are two spellings of one group, and
likewise for the two functorial actions. Everything below is written in the colimit spelling,
in which the library's generator lemmas are stated; the identification with the value of the
presheaf is definitional and is used only where the comparison map is assembled. The group of
sections supported on the graph likewise has the two spellings `H_Z(F)` and the value of the
diagram of Stacks 0F6M at that support, and `graphDiagramSection` pins the second. -/

/-- The section supported on the graph of `W → U`, as an element of the diagram of Stacks
0F6M at the index given by that graph. -/
public def graphDiagramSection (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) ⟶ (finiteSupportDiagram B U.obj.hom F
      ((smallEtalePostcompose B X hX U).obj W)).obj (etaleGraphFiniteSupport B X hX U W) :=
  AddCommGrpCat.ofHom (etaleGraphSection B X hX U F W)

/-- The graph-supported section, read in the diagram of Stacks 0F6M, is the graph-supported
section. -/
private theorem graphDiagramSection_apply
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (s : F.obj.obj (op W)) :
    (graphDiagramSection B X hX U F W s).val =
      (etaleGraphSection B X hX U F W s).val :=
  rfl

/-- **The graph generator.** A section of `F` over an étale object `W → U` determines a
section of `F` with finite support over `W` viewed as an étale object over `X`: the colimit
generator at the graph of `W → U`, carrying the section supported on that graph. -/
public def graphSectionToFiniteSupport
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    F.obj.obj (op W) ⟶
      colimit (finiteSupportDiagram B U.obj.hom F ((smallEtalePostcompose B X hX U).obj W)) :=
  graphDiagramSection B X hX U F W ≫
    colimit.ι (finiteSupportDiagram B U.obj.hom F ((smallEtalePostcompose B X hX U).obj W))
      (etaleGraphFiniteSupport B X hX U W)

/-- The graph generators are natural in the abelian sheaf. -/
public theorem graphSectionToFiniteSupport_naturality
    {F G : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    graphSectionToFiniteSupport B X hX U F W ≫
        colim.map (finiteSupportDiagramMap B U.obj.hom φ
          ((smallEtalePostcompose B X hX U).obj W)) =
      φ.hom.app (op W) ≫ graphSectionToFiniteSupport B X hX U G W := by
  have key : graphDiagramSection B X hX U F W ≫
      (finiteSupportDiagramMap B U.obj.hom φ ((smallEtalePostcompose B X hX U).obj W)).app
        (etaleGraphFiniteSupport B X hX U W) =
      φ.hom.app (op W) ≫ graphDiagramSection B X hX U G W := by
    ext s
    exact etaleGraphSection_naturality B X hX U φ W s
  rw [graphSectionToFiniteSupport, graphSectionToFiniteSupport, Category.assoc,
    colimit.ι_map, ← Category.assoc, key, Category.assoc]

/-- The graph generator over `W` restricts along `W' ⟶ W` to the graph generator over `W'`.
This is stated for an abstract base change datum so that the identification of the
base-changed support with the graph of `W'` can be eliminated by substitution. -/
private theorem graphSectionToFiniteSupport_restrict_aux
    {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (g : W' ⟶ W)
    (E : FiniteSupport B U.obj.hom ((smallEtalePostcompose B X hX U).obj W'))
    (m : finiteSupportOpenObject B U.obj.hom ((smallEtalePostcompose B X hX U).obj W') E ⟶
      finiteSupportOpenObject B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
        (etaleGraphFiniteSupport B X hX U W))
    (hm : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map m ≫
        (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
          (etaleGraphFiniteSupport B X hX U W)).ι =
      (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W') E).ι ≫
        (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
          ((smallEtaleBaseChange B U.obj.hom).map
            ((smallEtalePostcompose B X hX U).map g)))
    (r : (finiteSupportDiagram B U.obj.hom F
        ((smallEtalePostcompose B X hX U).obj W)).obj (etaleGraphFiniteSupport B X hX U W) ⟶
      (finiteSupportDiagram B U.obj.hom F
        ((smallEtalePostcompose B X hX U).obj W')).obj E)
    (hr : ∀ a, (r a).val = F.obj.map m.op a.val)
    (he : E = etaleGraphFiniteSupport B X hX U W') :
    graphDiagramSection B X hX U F W ≫ r ≫
        colimit.ι (finiteSupportDiagram B U.obj.hom F
          ((smallEtalePostcompose B X hX U).obj W')) E =
      F.obj.map g.op ≫ graphSectionToFiniteSupport B X hX U F W' := by
  subst he
  have hfac : etaleGraphIntoSupportOpen B X hX U W' ≫ m =
      g ≫ etaleGraphIntoSupportOpen B X hX U W := by
    apply (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map_injective
    apply (cancel_mono (finiteSupportOpen B U.obj.hom
      ((smallEtalePostcompose B X hX U).obj W)
      (etaleGraphFiniteSupport B X hX U W)).ι).mp
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hm,
      etaleGraphIntoSupportOpen_comp, ← Category.assoc, etaleGraphIntoSupportOpen_comp,
      etaleGraph_naturality]
  have key : graphDiagramSection B X hX U F W ≫ r =
      F.obj.map g.op ≫ graphDiagramSection B X hX U F W' := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    refine etaleGraphSection_ext B X hX U F W' _ _ ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hr,
      graphDiagramSection_apply, graphDiagramSection_apply, etaleGraphSection_restrict,
      ← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, hfac, op_comp,
      F.obj.map_comp, ConcreteCategory.comp_apply, etaleGraphSection_restrict]
  rw [graphSectionToFiniteSupport, ← Category.assoc, key, Category.assoc]

/-- The graph generators are compatible with restriction along a morphism of étale test
objects over `U`. -/
public theorem graphSectionToFiniteSupport_restrict
    {W W' : SmallEtale B U.obj.left.1 U.obj.left.property} (g : W' ⟶ W) :
    graphSectionToFiniteSupport B X hX U F W ≫
        finiteSupportBaseChangeHom B U.obj.hom F ((smallEtalePostcompose B X hX U).map g) =
      F.obj.map g.op ≫ graphSectionToFiniteSupport B X hX U F W' := by
  rw [graphSectionToFiniteSupport, Category.assoc, finiteSupportBaseChangeHom_ι]
  exact graphSectionToFiniteSupport_restrict_aux B X hX U F g
    (finiteSupportBaseChange B U.obj.hom F ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).support
    (finiteSupportBaseChange B U.obj.hom F ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).openMap
    (finiteSupportBaseChange B U.obj.hom F ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).openMap_commutes
    (AddCommGrpCat.ofHom (finiteSupportBaseChange B U.obj.hom F
      ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).sectionsMap)
    (finiteSupportBaseChange B U.obj.hom F ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).sectionsMap_apply
    (Subtype.ext ((finiteSupportBaseChange B U.obj.hom F
      ((smallEtalePostcompose B X hX U).map g)
      (etaleGraphFiniteSupport B X hX U W)).support_eq.trans
        (etaleGraphFiniteSupport_baseChange B X hX U g).symm))

/-- The graph generators, assembled into a morphism from `F` to the restriction along `U ⟶ X`
of the finite-support direct image of `F`. This is the datum the universal property of the
left Kan extension turns into the comparison map. -/
public def graphSectionPreunit :
    F.obj ⟶ (smallEtalePostcompose B X hX U).op ⋙
      (etaleFiniteSupportPresheaf B X hX U).obj F where
  app W := graphSectionToFiniteSupport B X hX U F W.unop
  naturality _ _ g := (graphSectionToFiniteSupport_restrict B X hX U F g.unop).symm

end Comparison

/-! ### Stacks 0F6Q: the canonical map and its value on generators -/

/-- **Stacks 0F6Q.** The canonical map `j_{p!} ⟶ f_{p!}` from the presheaf extension by zero
along the étale morphism `U ⟶ X` to the finite-support direct image presheaf, natural in the
abelian sheaf on the small étale site of `U`. It is the map the universal property of the left
Kan extension produces from the graph generators. -/
@[stacks 0F6Q "canonical natural presheaf map"]
public def etaleExtensionToFiniteSupport :
    abelianPresheafExtensionByZero B X hX U ⟶ etaleFiniteSupportPresheaf B X hX U where
  app F := (smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunit B X hX U F) ≫
    ((smallEtalePostcompose B X hX U).op.lanAdjunction AddCommGrpCat.{u + 1}).counit.app
      ((etaleFiniteSupportPresheaf B X hX U).obj F)
  naturality F G φ := by
    have hpre : φ.hom ≫ graphSectionPreunit B X hX U G =
        graphSectionPreunit B X hX U F ≫ Functor.whiskerLeft
          (smallEtalePostcompose B X hX U).op
          ((etaleFiniteSupportPresheaf B X hX U).map φ) := by
      refine NatTrans.ext (funext fun W => ?_)
      exact (graphSectionToFiniteSupport_naturality B X hX U φ W.unop).symm
    have hc := ((smallEtalePostcompose B X hX U).op.lanAdjunction
      AddCommGrpCat.{u + 1}).counit.naturality
        ((etaleFiniteSupportPresheaf B X hX U).map φ)
    change (smallEtalePostcompose B X hX U).op.lan.map (Functor.whiskerLeft
          (smallEtalePostcompose B X hX U).op
          ((etaleFiniteSupportPresheaf B X hX U).map φ)) ≫
        ((smallEtalePostcompose B X hX U).op.lanAdjunction
          AddCommGrpCat.{u + 1}).counit.app
          ((etaleFiniteSupportPresheaf B X hX U).obj G) =
      ((smallEtalePostcompose B X hX U).op.lanAdjunction
          AddCommGrpCat.{u + 1}).counit.app
          ((etaleFiniteSupportPresheaf B X hX U).obj F) ≫
        (etaleFiniteSupportPresheaf B X hX U).map φ at hc
    change (smallEtalePostcompose B X hX U).op.lan.map φ.hom ≫
        ((smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunit B X hX U G) ≫
          ((smallEtalePostcompose B X hX U).op.lanAdjunction
            AddCommGrpCat.{u + 1}).counit.app
            ((etaleFiniteSupportPresheaf B X hX U).obj G)) =
      ((smallEtalePostcompose B X hX U).op.lan.map (graphSectionPreunit B X hX U F) ≫
          ((smallEtalePostcompose B X hX U).op.lanAdjunction
            AddCommGrpCat.{u + 1}).counit.app
            ((etaleFiniteSupportPresheaf B X hX U).obj F)) ≫
        (etaleFiniteSupportPresheaf B X hX U).map φ
    rw [← Category.assoc, ← Functor.map_comp, hpre, Functor.map_comp, Category.assoc, hc,
      Category.assoc]

/-- **Stacks 0F6Q.** The value of the canonical map on a generator of the presheaf extension
by zero: the section of `F` over an étale object `W → U`, viewed in the summand of `j_{p!}F`
over `W` indexed by `W ⟶ U`, goes to the colimit generator of `colim_Z H_Z(F)` at the graph of
`W → U`, carrying the section supported on that graph. Naturality of the comparison then
extends the formula to every lift `V ⟶ U` of an arbitrary étale test object `V ⟶ X`. -/
@[stacks 0F6Q "graph-support formula on generators"]
public theorem etaleExtensionToFiniteSupport_on_graph
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1})
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) (s : F.obj.obj (op W)) :
    ((etaleExtensionToFiniteSupport B X hX U).app F).app
        (op ((smallEtalePostcompose B X hX U).obj W))
        (((smallEtalePostcompose B X hX U).op.lanUnit.app F.obj).app (op W) s) =
      colimit.ι (finiteSupportDiagram B U.obj.hom F ((smallEtalePostcompose B X hX U).obj W))
        (etaleGraphFiniteSupport B X hX U W) (etaleGraphSection B X hX U F W s) := by
  have h := (((smallEtalePostcompose B X hX U).op.lanAdjunction
    AddCommGrpCat.{u + 1}).homEquiv F.obj
      ((etaleFiniteSupportPresheaf B X hX U).obj F)).apply_symm_apply
      (graphSectionPreunit B X hX U F)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_symm_apply,
    Functor.lanAdjunction_unit] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op W)) s

/-! ### The graph-supported-section datum -/

/-- The graph of an étale object `W → U` inside the base change `U ×_X W`, the support it
carries, its factorization through the canonical open of that support, and the section of an
abelian sheaf supported on it, bundled with the identities characterising them. The first
projection of the graph is the identity of `W` and the second is the structure morphism
`W ⟶ U`; the support is the image of the graph, and restriction along the factorized graph
recovers the section the supported section was built from. -/
public structure GraphSupportedSectionData (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (U : SmallEtale B X hX)
    (W : SmallEtale B U.obj.left.1 U.obj.left.property) where
  /-- The support of `U ×_X W` carried by the graph of `W → U`. -/
  support : FiniteSupport B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
  /-- The graph of `W → U`, as a morphism of schemes `W ⟶ U ×_X W`. -/
  graph : (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj W ⟶
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).obj
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W))
  /-- The first projection of the graph is the identity of `W`. -/
  graph_fst : graph ≫ B.inclusion.map
      (pullback.fst ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) = 𝟙 _
  /-- The second projection of the graph is the structure morphism `W ⟶ U`. -/
  graph_snd : graph ≫ B.inclusion.map
      (pullback.snd ((smallEtalePostcompose B X hX U).obj W).obj.hom U.obj.hom) =
    B.inclusion.map W.obj.hom
  /-- The support is the image of the graph. -/
  graph_range : Set.range graph.base = support.1
  /-- The factorization of the graph through the canonical open of its support. -/
  graphIntoSupportOpen : W ⟶ finiteSupportOpenObject B U.obj.hom
    ((smallEtalePostcompose B X hX U).obj W) support
  /-- Composed with the inclusion of the canonical open, the factorized graph is the graph. -/
  graphIntoSupportOpen_comp :
    (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map graphIntoSupportOpen ≫
      (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W) support).ι =
    graph
  /-- Inside the canonical open of the support, the image of the factorized graph is exactly
  the support. -/
  graphIntoSupportOpen_range :
    Set.range ((SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map
      graphIntoSupportOpen).base =
    (finiteSupportOpen B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)
      support).ι.base ⁻¹' support.1
  /-- The section supported on the graph determined by a section over `W`. -/
  sections : ∀ F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1},
    F.obj.obj (op W) →+ supportedSections B U.obj.left.1 U.obj.left.property F
      (baseChange B U.obj.hom ((smallEtalePostcompose B X hX U).obj W)) support.1
      (finiteSupport_isLocallyClosed B U.obj.hom _ support)
  /-- Restriction along the factorized graph recovers the section the supported section was
  built from. -/
  sections_apply : ∀ (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) (s : F.obj.obj (op W)),
    F.obj.map graphIntoSupportOpen.op (sections F s).val = s

/-- **Stacks 0F6Q, the graph supports.** For an étale object `W → U` the graph of `W → U` is
an open immersion `W ⟶ U ×_X W` whose image is a support finite over `W`, and a section of an
abelian sheaf over `W` is a section supported on that graph. -/
@[stacks 0F6Q "graph supports"]
public def graphSupportedSection (W : SmallEtale B U.obj.left.1 U.obj.left.property) :
    GraphSupportedSectionData B X hX U W where
  support := etaleGraphFiniteSupport B X hX U W
  graph := B.inclusion.map (etaleGraphMap B X hX U W)
  graph_fst := etaleGraphMap_comp_fst B X hX U W
  graph_snd := etaleGraphMap_comp_snd B X hX U W
  graph_range := rfl
  graphIntoSupportOpen := etaleGraphIntoSupportOpen B X hX U W
  graphIntoSupportOpen_comp := etaleGraphIntoSupportOpen_comp B X hX U W
  graphIntoSupportOpen_range := etaleGraphIntoSupportOpen_range B X hX U W
  sections F := etaleGraphSection B X hX U F W
  sections_apply F s := etaleGraphSection_restrict B X hX U F W s

end AlgebraicGeometry.SmallEtale

end
