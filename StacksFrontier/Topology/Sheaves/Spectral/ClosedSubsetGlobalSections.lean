module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.SpectralPartition
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Sets
public import StacksFrontier.Topology.Sheaves.EpiMono.Defs
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections
public import StacksFrontier.Topology.Sheaves.Sheafify.Stalk
public import StacksFrontier.Topology.Sheaves.Spectral.CompactBasisColimit
public import StacksFrontier.Topology.Sheaves.Spectral.ConstructibleSheaves
public import StacksFrontier.Topology.Sheaves.Stalk.Constant
public import StacksFrontier.Topology.Spectral.ConstructiblyClosed

/-!
# Global sections on a closed subset of a spectral space

Let `Z` be a closed subset of a spectral space `X`. If the intersection of `Z` with the closure
of every point of `X` is connected, then restricting to `Z` is a bijection on global sections of
every sheaf of sets on `X`.

Injectivity is the observation that every point of `X` specialises to a point of `Z`, so a global
section is determined by its germs along `Z`. Surjectivity is proved by reducing the sheaf: every
sheaf of sets on a space with a basis of quasi-compact opens is a filtered colimit of sheaves with
a finite presentation by constant sheaves on quasi-compact opens, and global sections on a
spectral space commute with filtered colimits; a finitely presented sheaf embeds into a finite
product of pushforwards of finite constant sheaves from closed constructible subsets; and for such
a pushforward the extension problem is the extension of a locally constant function from a closed
subset of a spectral space, which is solved by repeatedly splitting the space along a closed
partition extending a partition of `Z`.

## Main definitions

* `Stacks.globalSectionsRestriction`: the canonical restriction map from global sections of a
  sheaf on `X` to global sections of its restriction to a subset `Z`.

## Main results

* `Stacks.bijective_globalSectionsRestriction_of_isConnected_inter_closure`: restriction to `Z`
  is a bijection on global sections, under the hypotheses above.

## Implementation notes

The restriction of a sheaf to `Z` is its pullback along the continuous inclusion `Z → X`, and the
restriction map on global sections is the component over the largest open of the unit of the
pullback–pushforward adjunction. The equality of section sets asserted by the source is therefore
stated as bijectivity of that canonical map rather than as an equality of types.

Sections of a constant sheaf are identified with locally constant functions by comparing the
constant sheaf with Mathlib's sheaf of continuous maps into the discrete space, which is an
isomorphism because both have the same stalks. That comparison, rather than a direct description
of the sheafification, is what makes the extension problem for a pushforward of a constant sheaf
into the purely topological statement `Stacks.exists_isLocallyConstant_extension`.

## References

* [Stacks Project, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

universe u

namespace Stacks

/-! ### Global sections of a product of sheaves -/

/-- Global sections of a product of sheaves of sets are the product of their global sections:
the global sections functor is a right adjoint, hence preserves products. -/
private noncomputable def globalSectionsProductEquiv (X : TopCat.{u})
    {ι : Type} (G : ι → TopCat.Sheaf (Type u) X) [HasProduct G] :
    (∏ᶜ G).obj.obj (op ⊤) ≃ (∀ i, (G i).obj.obj (op ⊤)) := by
  let Γ := (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤)
  let : Γ.IsRightAdjoint :=
    (constantSheafAdj (Opens.grothendieckTopology X) (Type u)
      (isTerminalTop (α := Opens X))).isRightAdjoint
  exact (PreservesProduct.iso Γ G).toEquiv.trans
    (Concrete.productEquiv (fun i => Γ.obj (G i)))

/-- Global sections of the pullback of a finite product of sheaves of sets are the product of the
global sections of the pullbacks, because pullback preserves finite products. -/
private noncomputable def pullbackProductSectionsEquiv {X Y : TopCat.{u}}
    (f : Y ⟶ X) (n : ℕ) (G : Fin n → TopCat.Sheaf (Type u) X) [HasProduct G] :
    ((TopCat.Sheaf.pullback (Type u) f).obj (∏ᶜ G)).obj.obj (op ⊤) ≃
      (∀ i, ((TopCat.Sheaf.pullback (Type u) f).obj (G i)).obj.obj (op ⊤)) := by
  let : PreservesFiniteLimits (TopCat.Sheaf.pullback (Type u) f) :=
    pullbackPreservesFiniteLimits f
  let : HasFiniteProducts (TopCat.Sheaf (Type u) Y) :=
    CategoryTheory.Sheaf.instHasFiniteProducts
  let ΓY := (sheafSections (Opens.grothendieckTopology Y) (Type u)).obj (op ⊤)
  exact (ΓY.mapIso (PreservesProduct.iso (TopCat.Sheaf.pullback (Type u) f) G)).toEquiv.trans
    (globalSectionsProductEquiv Y (fun i : Fin n => (TopCat.Sheaf.pullback (Type u) f).obj (G i)))

/-- The components of `Stacks.globalSectionsProductEquiv` are the projections of the product. -/
private lemma globalSectionsProductEquiv_apply (X : TopCat.{u})
    {ι : Type} (G : ι → TopCat.Sheaf (Type u) X) [HasProduct G]
    (s : (∏ᶜ G).obj.obj (op ⊤)) (i : ι) :
    (globalSectionsProductEquiv X G s) i = (Pi.π G i).hom.app (op ⊤) s := by
  let Γ := (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤)
  let : Γ.IsRightAdjoint :=
    (constantSheafAdj (Opens.grothendieckTopology X) (Type u)
      (isTerminalTop (α := Opens X))).isRightAdjoint
  change (Concrete.productEquiv (fun j => Γ.obj (G j)))
      ((PreservesProduct.iso Γ G).hom s) i = _
  rw [Concrete.productEquiv_apply_apply]
  change (ConcreteCategory.hom
    ((PreservesProduct.iso Γ G).hom ≫ Pi.π (fun j => Γ.obj (G j)) i)) s = _
  exact ConcreteCategory.congr_hom (piComparison_comp_π Γ G i) s

/-- The components of `Stacks.pullbackProductSectionsEquiv` are the pullbacks of the projections
of the product. -/
private lemma pullbackProductSectionsEquiv_apply {X Y : TopCat.{u}}
    (f : Y ⟶ X) (n : ℕ) (G : Fin n → TopCat.Sheaf (Type u) X) [HasProduct G]
    (t : ((TopCat.Sheaf.pullback (Type u) f).obj (∏ᶜ G)).obj.obj (op ⊤))
    (i : Fin n) :
    (pullbackProductSectionsEquiv f n G t) i =
      (((TopCat.Sheaf.pullback (Type u) f).map (Pi.π G i)).hom.app (op ⊤)) t := by
  let H := TopCat.Sheaf.pullback (Type u) f
  let Γ := (sheafSections (Opens.grothendieckTopology Y) (Type u)).obj (op ⊤)
  let : PreservesFiniteLimits H := pullbackPreservesFiniteLimits f
  let : HasFiniteProducts (TopCat.Sheaf (Type u) Y) :=
    CategoryTheory.Sheaf.instHasFiniteProducts
  change (globalSectionsProductEquiv Y (fun j : Fin n => H.obj (G j)))
      ((Γ.mapIso (PreservesProduct.iso H G)).hom t) i = _
  rw [globalSectionsProductEquiv_apply]
  change (ConcreteCategory.hom
    (((PreservesProduct.iso H G).hom ≫ Pi.π (fun j => H.obj (G j)) i).hom.app (op ⊤))) t = _
  exact congrArg (fun q : H.obj (∏ᶜ G) ⟶ H.obj (G i) =>
    ConcreteCategory.hom (q.hom.app (op ⊤)) t) (piComparison_comp_π H G i)

/-! ### Global sections on a spectral space commute with filtered colimits -/

/-- On a spectral space every open cover of the whole space admits a finite refinement by
quasi-compact opens with quasi-compact pairwise intersections. -/
private lemma top_hasFiniteCompactCofinalCovers {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] :
    DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := TopCat.of X) ⊤ := by
  intro J V hVU hcover
  let A : Type u := Σ j : J, {U : Set X // IsOpen U ∧ IsCompact U ∧ U ⊆ (V j : Set X)}
  have hAcover : (Set.univ : Set X) ⊆ ⋃ a : A, (a.2.1 : Set X) := by
    intro x hx
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hcover hx)
    obtain ⟨U, ⟨hUopen, hUcompact⟩, hxU, hUV⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxj (V j).2
    exact Set.mem_iUnion.mpr ⟨⟨j, ⟨U, hUopen, hUcompact, hUV⟩⟩, hxU⟩
  have hopenA : ∀ a : A, IsOpen (a.2.1 : Set X) := fun a => a.2.2.1
  have hcoverA : IsOpenCover (fun a : A => Opens.mk (a.2.1 : Set X) (hopenA a)) := by
    change (⨆ a : A, Opens.mk (a.2.1 : Set X) (hopenA a)) = ⊤
    ext x
    refine ⟨fun _ => by simp, fun _ => ?_⟩
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (hAcover (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨a, hxa⟩
  obtain ⟨t, ht⟩ := hcoverA.exists_finite_of_compactSpace
  let K := {a : A // a ∈ t}
  let W : K → Opens (TopCat.of X) := fun a => ⟨a.val.2.val, a.val.2.property.1⟩
  refine ⟨K, inferInstance, W, fun _ => le_top, fun x _ => ?_,
    fun a => ⟨a.val.1, a.val.2.property.2.2⟩, fun a a' => ?_⟩
  · change x ∈ (⨆ k, W k : Opens (TopCat.of X))
    rw [ht]
    simp
  · simpa [W] using IsCompact.inter_of_isOpen a.val.2.property.2.1
      a'.val.2.property.2.1 a.val.2.property.1 a'.val.2.property.1

/-- A morphism out of a sheafification is an isomorphism on the stalk at `x` as soon as its
composite with the unit of sheafification is. -/
private theorem isIso_stalkFunctor_map_of_toSheafify_comp {X : TopCat.{u}}
    (P : TopCat.Presheaf (Type u) X) {Q : TopCat.Presheaf (Type u) X}
    (θ : ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).obj P).obj ⟶ Q) (x : X)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (toSheafify (Opens.grothendieckTopology X) P ≫ θ))) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map θ) := by
  have : IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (toSheafify (Opens.grothendieckTopology X) P)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) P
  rw [Functor.map_comp] at h
  exact (isIso_comp_left_iff _ _).mp h

/-- The sheafification of a presheaf of sets on a space agrees with the site-theoretic
sheafification, because the comparison map is an isomorphism on all stalks. -/
private noncomputable def concreteSheafifyIso {X : TopCat.{u}}
    (P : TopCat.Presheaf (Type u) X) :
    (presheafToSheaf (Opens.grothendieckTopology X) (Type u)).obj P ≅ P.sheafify := by
  let J := Opens.grothendieckTopology X
  let adj := sheafificationAdjunction J (Type u)
  let θ : (presheafToSheaf J (Type u)).obj P ⟶ P.sheafify :=
    (adj.homEquiv P P.sheafify).symm P.toSheafify
  have htri : toSheafify J P ≫ θ.hom = P.toSheafify :=
    (adj.homEquiv P P.sheafify).apply_symm_apply P.toSheafify
  have : IsIso θ := by
    let : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map θ.hom) := fun x =>
      isIso_stalkFunctor_map_of_toSheafify_comp P θ.hom x (by
        rw [htri]
        exact stalkFunctor_map_toSheafify_isIso P x)
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso θ
  exact asIso θ

/-- For a filtered diagram of sheaves of sets on a space all of whose covers of the whole space
refine to finite covers by quasi-compact opens, global sections of the colimit are the colimit of
the global sections: the sheafification cocone stays a colimit after taking global sections. -/
private noncomputable def globalSections_isColimit_sheafifyCocone
    {X : TopCat.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ TopCat.Sheaf (Type u) X)
    (hX : DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤) :
    let P := DirectedColimitOfSheaves.presheafSystem D
    let c := CategoryTheory.Sheaf.sheafifyCocone (colimit.cocone P)
    let Γ := (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤)
    IsColimit (Γ.mapCocone c) := by
  dsimp only
  let P := DirectedColimitOfSheaves.presheafSystem D
  let E := (evaluation ((Opens X)ᵒᵖ) (Type u)).obj (op ⊤)
  let cP := colimit.cocone P
  let c := CategoryTheory.Sheaf.sheafifyCocone cP
  let Γ := (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤)
  have hE : IsColimit (E.mapCocone cP) :=
    isColimitOfPreserves E (colimit.isColimit P)
  let θ := concreteSheafifyIso cP.pt
  let eθ := (Γ.mapIso θ).toEquiv
  have hb := DirectedColimitOfSheaves.bijective_canonicalMap_of_hasFiniteCompactCofinalCovers
    D ⊤ hX
  let ψ := DirectedColimitOfSheaves.canonicalMap D ⊤
  let e : (E.mapCocone cP).pt ≃ (Γ.mapCocone c).pt :=
    (Equiv.ofBijective ψ hb).trans eθ.symm
  let hL := Functor.coconeTypesEquiv_symm_apply_pt (P ⋙ E) (E.mapCocone cP)
  let hR := Functor.coconeTypesEquiv_symm_apply_pt (D ⋙ Γ) (Γ.mapCocone c)
  let e' : ((P ⋙ E).coconeTypesEquiv.symm (E.mapCocone cP)).pt ≃
      ((D ⋙ Γ).coconeTypesEquiv.symm (Γ.mapCocone c)).pt :=
    ((Equiv.cast hL).trans e).trans (Equiv.cast hR.symm)
  refine ((Types.isColimit_iff_coconeTypesIsColimit (Γ.mapCocone c)).2 ?_).some
  apply ((Types.isColimit_iff_coconeTypesIsColimit (E.mapCocone cP)).1 ⟨hE⟩).of_equiv e'
  intro j x
  apply eθ.injective
  refine Eq.trans ?_ (eθ.apply_symm_apply (ψ (E.map (cP.ι.app j) x))).symm
  change θ.hom.hom.app (op ⊤) ((c.ι.app j).hom.app (op ⊤) x) =
    cP.pt.toSheafify.app (op ⊤) ((cP.ι.app j).app (op ⊤) x)
  have htri : toSheafify (Opens.grothendieckTopology X) cP.pt ≫ θ.hom.hom =
      cP.pt.toSheafify :=
    ((sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)).homEquiv
      cP.pt cP.pt.sheafify).apply_symm_apply cP.pt.toSheafify
  exact (congrArg (fun q => θ.hom.hom.app (op ⊤) (q.app (op ⊤) x))
      (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val cP j)).trans
    (congrArg (fun q => q.app (op ⊤) ((cP.ι.app j).app (op ⊤) x)) htri)

/-- Global sections preserve a filtered colimit of sheaves of sets on a space all of whose covers
of the whole space refine to finite covers by quasi-compact opens. -/
private theorem globalSections_preservesFilteredColimit
    {X : TopCat.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ TopCat.Sheaf (Type u) X)
    (hX : DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimit D
      ((sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤)) := by
  let P := DirectedColimitOfSheaves.presheafSystem D
  exact preservesColimit_of_preserves_colimit_cocone
    (CategoryTheory.Sheaf.isColimitSheafifyCocone (colimit.cocone P)
      (colimit.isColimit P))
    (globalSections_isColimit_sheafifyCocone D hX)

/-! ### Closed subspaces of a spectral space -/

/-- A closed subset of a prespectral space is closed in the constructible topology. -/
private theorem isClosed_constructibleTopology_of_isClosed {X : Type*} [TopologicalSpace X]
    [PrespectralSpace X] {Z : Set X} (hZ : IsClosed Z) :
    @IsClosed X (constructibleTopology X) Z := by
  obtain ⟨S, hS, hU⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion hZ.isOpen_compl
  have hEach : ∀ U ∈ S, @IsOpen X (constructibleTopology X) U := fun _ hUS =>
    (hS hUS).2.isOpen_constructibleTopology_of_isOpen (hS hUS).1
  have hOpen : @IsOpen X (constructibleTopology X) Zᶜ := by
    rw [hU]
    let : TopologicalSpace X := constructibleTopology X
    exact isOpen_sUnion hEach
  let : TopologicalSpace X := constructibleTopology X
  simpa only [compl_compl] using hOpen.isClosed_compl

/-- A closed subspace of a spectral space is spectral. -/
private theorem spectralSpace_closed_subtype {X : Type*} [TopologicalSpace X]
    [SpectralSpace X] (Z : Set X) (hZ : IsClosed Z) : SpectralSpace Z :=
  spectralSpace_of_isClosed_constructibleTopology Z
    (isClosed_constructibleTopology_of_isClosed hZ)

/-- The connectedness hypothesis on `Z` passes to a closed subspace `Y`: the trace of `Z` on `Y`
meets the closure of every point of `Y` in a connected set, because the closure of a point of `Y`
is contained in `Y`. -/
private theorem isConnected_inter_closure_closed_subtype {X : Type*} [TopologicalSpace X]
    {Y Z : Set X} (hY : IsClosed Y)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) :
    ∀ y : Y, IsConnected ({z : Y | (z : X) ∈ Z} ∩ closure ({y} : Set Y)) := by
  intro y
  let C : Set X := Z ∩ closure ({(y : X)} : Set X)
  have hcl : closure ({(y : X)} : Set X) ⊆ Y :=
    closure_minimal (Set.singleton_subset_iff.mpr y.2) hY
  have hCY : C ⊆ Set.range (Subtype.val : Y → X) := fun z hz => ⟨⟨z, hcl hz.2⟩, rfl⟩
  have hpre : IsConnected ((Subtype.val : Y → X) ⁻¹' C) :=
    (hconn y.1).preimage_of_isClosedMap Subtype.val_injective
      hY.isClosedEmbedding_subtypeVal.isClosedMap hCY
  have heq : ({z : Y | (z : X) ∈ Z} ∩ closure ({y} : Set Y)) =
      (Subtype.val : Y → X) ⁻¹' C := by
    ext z
    simp [C, Set.mem_inter_iff, closure_subtype]
  exact heq ▸ hpre

/-- **Stacks Project, Tag 09ZG**, the underlying topological statement. A locally constant
function on a closed subset `Z` of a spectral space extends to a locally constant function on the
whole space, provided `Z` meets the closure of every point in a connected set.

Each fibre of the function and its complement in `Z` form a relatively closed partition of `Z`,
which extends to a closed partition of the ambient space; the resulting pieces are open as well
as closed, and the connectedness hypothesis makes exactly one of them contain each point. -/
private lemma exists_isLocallyConstant_extension
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    {S : Type u} (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (f : Z → S) (hf : IsLocallyConstant f) :
    ∃ g : X → S, IsLocallyConstant g ∧ ∀ z : Z, g z.1 = f z := by
  let A (s : S) : Set X := {x | ∃ z : Z, z.1 = x ∧ f z = s}
  let B (s : S) : Set X := Z \ A s
  have hApre (s : S) :
      (Subtype.val : Z → X) ⁻¹' A s = {z : Z | f z = s} := by
    ext z
    refine ⟨?_, fun hz => ⟨z, rfl, hz⟩⟩
    rintro ⟨z', hz', hf'⟩
    obtain rfl := Subtype.ext hz'
    exact hf'
  have hAclosed (s : S) : IsClosed ((Subtype.val : Z → X) ⁻¹' A s) := by
    rw [hApre]
    exact hf.isClopen_fiber s |>.1
  have hBclosed (s : S) : IsClosed ((Subtype.val : Z → X) ⁻¹' B s) := by
    have hb : (Subtype.val : Z → X) ⁻¹' B s =
        ((Subtype.val : Z → X) ⁻¹' A s)ᶜ := by
      ext z
      simp [B]
    rw [hb, hApre]
    exact (hf.isClopen_fiber s).2.isClosed_compl
  have hAZ (s : S) : A s ⊆ Z := by
    rintro x ⟨z, rfl, _⟩
    exact z.2
  have hAB (s : S) : A s ∪ B s = Z := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, B]
    exact ⟨fun h => h.elim (hAZ s ·) And.left,
      fun hx => (em (x ∈ A s)).imp_right fun ha => ⟨hx, ha⟩⟩
  have hdisj (s : S) : Disjoint (A s) (B s) := Set.disjoint_left.mpr fun _ ha hb => hb.2 ha
  have hext (s : S) := _root_.exists_isClosed_partition hZ hconn
    (hAclosed s) (hBclosed s) (hAB s) (hdisj s)
  choose P Q hPc hQc hcover hPQ hPA hQB using hext
  have hmem (s : S) (x : X) : x ∈ P s ∪ Q s := (hcover s).symm ▸ Set.mem_univ x
  have hPopen (s : S) : IsOpen (P s) := by
    have hpq : P s = (Q s)ᶜ := by
      ext x
      constructor
      · intro hp hq
        exact Set.disjoint_left.mp (hPQ s) hp hq
      · exact fun hnq => (hmem s x).resolve_right hnq
    rw [hpq]
    exact (hQc s).isOpen_compl
  have hP (s : S) (x : X) (z : X) (hz : z ∈ Z)
      (hsp : x ⤳ z) : x ∈ P s ↔ f ⟨z, hz⟩ = s := by
    constructor
    · intro hp
      have hzp : z ∈ P s := hsp.mem_closed (hPc s) hp
      have hza : z ∈ A s := (hPA s).symm ▸ ⟨hz, hzp⟩
      rcases hza with ⟨z', hz', hf'⟩
      have : z' = (⟨z, hz⟩ : Z) := Subtype.ext hz'
      simpa [this] using hf'
    · intro hfs
      have hza : z ∈ A s := ⟨⟨z, hz⟩, rfl, hfs⟩
      have hzp : z ∈ P s := ((hPA s) ▸ hza).2
      by_contra hxp
      have hzq : z ∈ Q s := hsp.mem_closed (hQc s) ((hmem s x).resolve_left hxp)
      exact Set.disjoint_left.mp (hPQ s) hzp hzq
  have hex (x : X) : ∃! s : S, x ∈ P s := by
    obtain ⟨z, hz, hzx⟩ := (hconn x).nonempty
    have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hzx
    exact ⟨f ⟨z, hz⟩, (hP _ x z hz hsp).2 rfl, fun t ht => ((hP t x z hz hsp).1 ht).symm⟩
  let g : X → S := fun x => Classical.choose (hex x)
  have hgP (s : S) : g ⁻¹' {s} = P s := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ((Classical.choose_spec (hex x)).2 s hx).symm⟩
    rw [← show g x = s from hx]
    exact (Classical.choose_spec (hex x)).1
  refine ⟨g, IsLocallyConstant.iff_isOpen_fiber.mpr fun s => hgP s ▸ hPopen s, fun z => ?_⟩
  exact ((hP (g z) z z z.2 (specializes_refl (z : X))).1 (Classical.choose_spec (hex z)).1).symm

/-! ### Constant sheaves and locally constant functions -/

/-- The pullback of a constant sheaf of sets is the constant sheaf with the same value: both are
left adjoint to taking global sections. -/
private noncomputable def constantSheafPullbackIso {X Y : TopCat.{u}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (Type u) ⋙
      TopCat.Sheaf.pullback (Type u) f ≅
    constantSheaf (Opens.grothendieckTopology X) (Type u) :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
    (isTerminalTop (α := Opens Y))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) (Type u)
      (isTerminalTop (α := Opens X)))

/-- The map from the constant presheaf with value `S` to the presheaf of continuous maps into the
discrete space `S`, sending a value to the constant map with that value. -/
private noncomputable def constantToContinuousPresheaf (X : TopCat.{u}) (S : Type u) :
    constantPresheafOnSpace X (Type u) S ⟶
      (TopCat.sheafToTop (X := X) (TopCat.discrete.obj S)).presheaf := by
  let : TopologicalSpace S := ⊥
  refine { app := fun U => ↾fun s => TopCat.ofHom (ContinuousMap.const _ s), naturality := ?_ }
  intro U V f
  ext s
  rfl

/-- The map from the constant sheaf with value `S` to the sheaf of continuous maps into the
discrete space `S`, obtained from `Stacks.constantToContinuousPresheaf` by the universal property
of sheafification. -/
private noncomputable def constantToContinuousSheaf (X : TopCat.{u}) (S : Type u) :
    constantSheafOnSpace X (Type u) S ⟶
      TopCat.sheafToTop (X := X) (TopCat.discrete.obj S) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)).homEquiv
    (constantPresheafOnSpace X (Type u) S)
    (TopCat.sheafToTop (X := X) (TopCat.discrete.obj S))).symm
      (constantToContinuousPresheaf X S)

/-- `Stacks.constantToContinuousPresheaf` is bijective on all stalks: both stalks are `S`, the
source because the stalks of a constant presheaf are its value and the target because a continuous
map into a discrete space is constant near each point. -/
private theorem constantToContinuousPresheaf_stalk_bijective (X : TopCat.{u}) (S : Type u)
    (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (constantToContinuousPresheaf X S)) := by
  have hα : Function.Bijective (fun s : S =>
      (constantPresheafOnSpace X (Type u) S).germ ⊤ x trivial s) :=
    alphaX_bijective X S x
  let P := (sheafToTop (X := X) (TopCat.discrete.obj S)).presheaf
  constructor
  · intro a b hab
    obtain ⟨sa, rfl⟩ := hα.2 a
    obtain ⟨sb, rfl⟩ := hα.2 b
    have ha := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      (constantToContinuousPresheaf X S) sa
    have hb := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      (constantToContinuousPresheaf X S) sb
    rw [ha, hb] at hab
    obtain ⟨W, hW, iU, iV, hmap⟩ := P.germ_eq x (by trivial) (by trivial)
      ((constantToContinuousPresheaf X S).app (op ⊤) sa)
      ((constantToContinuousPresheaf X S).app (op ⊤) sb) hab
    have he := congrArg (fun q : P.obj (op W) => (ConcreteCategory.hom q) ⟨x, hW⟩) hmap
    exact congrArg _ (he : sa = sb)
  · intro t
    obtain ⟨U, hx, f, ht⟩ := P.exists_germ_eq t
    let a : S := (ConcreteCategory.hom f) ⟨x, hx⟩
    let E : Set U := {y | (ConcreteCategory.hom f) y = a}
    have hEopen : IsOpen E := by
      have : TopologicalSpace S := ⊥
      exact (ConcreteCategory.hom f).continuous.isOpen_preimage {a} (isOpen_discrete _)
    let W : Opens X := ⟨Subtype.val '' E, U.2.isOpenMap_subtype_val E hEopen⟩
    have hxW : x ∈ W := ⟨⟨x, hx⟩, rfl, rfl⟩
    have hWU : W ≤ U := by
      rintro y ⟨z, hzE, rfl⟩
      exact z.2
    have hconst : P.map (homOfLE hWU).op f =
        (constantToContinuousPresheaf X S).app (op W) a := by
      apply TopCat.Hom.ext
      ext y
      rcases y.2 with ⟨z, hzE, hz⟩
      have hz' : z = (⟨y.1, hWU y.2⟩ : U) := Subtype.ext hz
      change (ConcreteCategory.hom f) ⟨y.1, hWU y.2⟩ = a
      change (ConcreteCategory.hom f) z = a at hzE
      simpa [hz'] using hzE
    refine ⟨(constantPresheafOnSpace X (Type u) S).germ ⊤ x trivial a, ?_⟩
    have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      (constantToContinuousPresheaf X S) a
    have htop : P.germ ⊤ x trivial ((constantToContinuousPresheaf X S).app (op ⊤) a) =
        P.germ W x hxW ((constantToContinuousPresheaf X S).app (op W) a) := by
      have hc : P.map (homOfLE le_top).op
          ((constantToContinuousPresheaf X S).app (op ⊤) a) =
            (constantToContinuousPresheaf X S).app (op W) a := by
        apply TopCat.Hom.ext
        ext y
        rfl
      rw [← hc]
      exact (P.germ_res_apply (homOfLE le_top) x hxW
        ((constantToContinuousPresheaf X S).app (op ⊤) a)).symm
    have hmid : P.germ W x hxW ((constantToContinuousPresheaf X S).app (op W) a) =
        P.germ W x hxW (P.map (homOfLE hWU).op f) := by rw [hconst]
    exact hmap.trans (htop.trans (hmid.trans
      ((P.germ_res_apply (homOfLE hWU) x hxW f).trans ht)))

/-- The constant sheaf with value `S` is the sheaf of continuous maps into the discrete space
`S`. -/
private theorem constantToContinuousSheaf_isIso (X : TopCat.{u}) (S : Type u) :
    IsIso (constantToContinuousSheaf X S) := by
  let : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map
      (constantToContinuousSheaf X S).hom) := by
    intro x
    refine isIso_stalkFunctor_map_of_toSheafify_comp (constantPresheafOnSpace X (Type u) S)
      (constantToContinuousSheaf X S).hom x ?_
    rw [show toSheafify (Opens.grothendieckTopology X) (constantPresheafOnSpace X (Type u) S) ≫
        (constantToContinuousSheaf X S).hom = constantToContinuousPresheaf X S from
      ((sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)).homEquiv _ _
        ).apply_symm_apply _]
    exact (bijective_iff_isIso_ofHom _).mp (constantToContinuousPresheaf_stalk_bijective X S x)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- The global section of the constant sheaf with value `S` corresponding to a locally constant
function `X → S`. -/
private noncomputable def constantSectionOfLocallyConstant
    (X : TopCat.{u}) (S : Type u) (f : LocallyConstant X S) :
    (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤) := by
  let : TopologicalSpace S := ⊥
  have : IsIso (constantToContinuousSheaf X S) :=
    constantToContinuousSheaf_isIso X S
  exact (asIso (constantToContinuousSheaf X S)).inv.hom.app (op ⊤)
    (TopCat.ofHom
      ⟨fun x : (⊤ : Opens X) => f x.1,
        f.isLocallyConstant.continuous.comp continuous_subtype_val⟩)

/-- The locally constant function `X → S` underlying a global section of the constant sheaf with
value `S`. -/
private noncomputable def locallyConstantOfConstantSection
    (X : TopCat.{u}) (S : Type u)
    (s : (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤)) :
    LocallyConstant X S := by
  let : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let t := (constantToContinuousSheaf X S).hom.app (op ⊤) s
  let htop : Continuous (fun x : X => (⟨x, by simp⟩ : (⊤ : Opens X))) :=
    Continuous.subtype_mk continuous_id (fun _ => by simp)
  have hc : Continuous (fun x : X => (ConcreteCategory.hom t) ⟨x, by simp⟩) :=
    t.hom.continuous.comp htop
  exact ⟨fun x => (ConcreteCategory.hom t) ⟨x, by simp⟩,
    IsLocallyConstant.iff_isOpen_fiber.mpr (fun a =>
      hc.isOpen_preimage {a} (isOpen_discrete _))⟩

/-- Passing from a locally constant function to a global constant section and back is the
identity. -/
private theorem locallyConstantOfConstantSection_sectionOf
    (X : TopCat.{u}) (S : Type u) (f : LocallyConstant X S) :
    locallyConstantOfConstantSection X S (constantSectionOfLocallyConstant X S f) = f := by
  let : TopologicalSpace S := ⊥
  have : IsIso (constantToContinuousSheaf X S) :=
    constantToContinuousSheaf_isIso X S
  let e := asIso (constantToContinuousSheaf X S)
  apply LocallyConstant.ext
  intro x
  let t : (sheafToTop (X := X) (TopCat.discrete.obj S)).obj.obj (op ⊤) :=
    TopCat.ofHom ⟨fun y : (⊤ : Opens X) => f y.1,
      f.isLocallyConstant.continuous.comp continuous_subtype_val⟩
  have h := congrArg (fun q => q.hom.app (op ⊤) t) e.inv_hom_id
  change e.hom.hom.app (op ⊤) (e.inv.hom.app (op ⊤) t) = t at h
  change (ConcreteCategory.hom
    (e.hom.hom.app (op ⊤) (e.inv.hom.app (op ⊤) t))) ⟨x, by simp⟩ = f x
  rw [h]
  rfl

/-- Passing from a global constant section to a locally constant function and back is the
identity. -/
private theorem constantSectionOfLocallyConstant_ofSection
    (X : TopCat.{u}) (S : Type u)
    (s : (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤)) :
    constantSectionOfLocallyConstant X S (locallyConstantOfConstantSection X S s) = s := by
  let : TopologicalSpace S := ⊥
  have : IsIso (constantToContinuousSheaf X S) :=
    constantToContinuousSheaf_isIso X S
  let e := asIso (constantToContinuousSheaf X S)
  let t : (sheafToTop (X := X) (TopCat.discrete.obj S)).obj.obj (op ⊤) :=
    e.hom.hom.app (op ⊤) s
  have ht : (TopCat.ofHom
      ⟨fun x : (⊤ : Opens X) => (locallyConstantOfConstantSection X S s) x.1,
        (locallyConstantOfConstantSection X S s).isLocallyConstant.continuous.comp
          continuous_subtype_val⟩ :
      (sheafToTop (X := X) (TopCat.discrete.obj S)).obj.obj (op ⊤)) = t := by
    apply TopCat.Hom.ext
    ext x
    rfl
  change e.inv.hom.app (op ⊤) _ = s
  rw [ht]
  exact congrArg (fun q => q.hom.app (op ⊤) s) e.hom_inv_id

/-- Global sections of the constant sheaf with value `S` are the locally constant functions with
values in `S`. -/
private noncomputable def constantSectionsEquivLocallyConstant
    (X : TopCat.{u}) (S : Type u) :
    (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤) ≃ LocallyConstant X S where
  toFun := locallyConstantOfConstantSection X S
  invFun := constantSectionOfLocallyConstant X S
  left_inv := constantSectionOfLocallyConstant_ofSection X S
  right_inv := locallyConstantOfConstantSection_sectionOf X S

/-- The global section of the constant sheaf with value `S` given by a single element of `S`. -/
private noncomputable def globalConstantSection (X : TopCat.{u})
    (S : Type u) (a : S) :
    (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤) :=
  (toSheafify (Opens.grothendieckTopology X)
    (constantPresheafOnSpace X (Type u) S)).app (op ⊤) a

/-- Every germ of the constant sheaf with value `S` is the germ of a
`Stacks.globalConstantSection`, because the stalks of a constant presheaf are already its value. -/
private lemma exists_globalConstantSection_germ_eq
    (X : TopCat.{u}) (S : Type u)
    (s : (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤)) (x : X) :
    let F : TopCat.Sheaf (Type u) X := constantSheafOnSpace X (Type u) S
    ∃ a : S, F.presheaf.germ ⊤ x trivial s =
      F.presheaf.germ ⊤ x trivial (globalConstantSection X S a) := by
  let F : TopCat.Sheaf (Type u) X := constantSheafOnSpace X (Type u) S
  change ∃ a : S, F.presheaf.germ ⊤ x trivial s =
    F.presheaf.germ ⊤ x trivial (globalConstantSection X S a)
  let P := constantPresheafOnSpace X (Type u) S
  let η := toSheafify (Opens.grothendieckTopology X) P
  let c := (TopCat.Presheaf.stalkFunctor (Type u) x).map η
  have : IsIso c :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) P
  obtain ⟨a, ha⟩ := (alphaX_bijective X S x).2 ((inv c) (F.presheaf.germ ⊤ x trivial s))
  refine ⟨a, (IsIso.inv_hom_id_apply c _).symm.trans ((congrArg c ha.symm).trans ?_)⟩
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial η a

/-- The comparison with the sheaf of continuous maps sends a `Stacks.globalConstantSection` to the
constant map. -/
private lemma constantToContinuousSheaf_globalConstantSection
    (X : TopCat.{u}) (S : Type u) (a : S) :
    (constantToContinuousSheaf X S).hom.app (op ⊤)
      (globalConstantSection X S a) =
        (constantToContinuousPresheaf X S).app (op ⊤) a := by
  let P := constantPresheafOnSpace X (Type u) S
  let H := TopCat.sheafToTop (X := X) (TopCat.discrete.obj S)
  let adj := sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)
  exact congrArg (fun q => q.app (op ⊤) a)
    ((adj.homEquiv P H).apply_symm_apply (constantToContinuousPresheaf X S))

/-- The locally constant function underlying a `Stacks.globalConstantSection` is constant. -/
private lemma locallyConstantOfConstantSection_globalConstantSection
    (X : TopCat.{u}) (S : Type u) (a : S) (x : X) :
    locallyConstantOfConstantSection X S (globalConstantSection X S a) x = a := by
  change (ConcreteCategory.hom
    ((constantToContinuousSheaf X S).hom.app (op ⊤)
      (globalConstantSection X S a))) ⟨x, by simp⟩ = a
  rw [constantToContinuousSheaf_globalConstantSection]
  rfl

/-- Two global sections of a constant sheaf with the same germ at `x` have the same value at
`x`. -/
private lemma locallyConstantOfConstantSection_eq_of_germ
    (X : TopCat.{u}) (S : Type u) (x : X)
    (s t : (constantSheafOnSpace X (Type u) S).obj.obj (op ⊤))
    (h : let F : TopCat.Sheaf (Type u) X := constantSheafOnSpace X (Type u) S
      F.presheaf.germ ⊤ x trivial s = F.presheaf.germ ⊤ x trivial t) :
    locallyConstantOfConstantSection X S s x =
      locallyConstantOfConstantSection X S t x := by
  let H := sheafToTop (X := X) (TopCat.discrete.obj S)
  let m := (constantToContinuousSheaf X S).hom
  have hm : H.presheaf.germ ⊤ x (Set.mem_univ x) (m.app (op ⊤) s) =
      H.presheaf.germ ⊤ x (Set.mem_univ x) (m.app (op ⊤) t) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Set.mem_univ x) m s).symm.trans
      ((congrArg (fun q => ((TopCat.Presheaf.stalkFunctor (Type u) x).map m) q) h).trans
        (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Set.mem_univ x) m t))
  obtain ⟨W, hxW, i₁, i₂, heq⟩ := H.presheaf.germ_eq x
    (Set.mem_univ x) (Set.mem_univ x)
    (m.app (op ⊤) s) (m.app (op ⊤) t) hm
  exact congrArg (fun q : H.obj.obj (op W) => (ConcreteCategory.hom q) ⟨x, hxW⟩) heq

/-! ### Lifting a section along a monomorphism of sheaves -/

/-- A section of the target of a monomorphism of sheaves of sets that lifts locally on a cover
lifts globally: the local lifts are compatible because the map is injective on sections. -/
private theorem section_lift_of_local_sections {X : TopCat.{u}}
    {F G : TopCat.Sheaf (Type u) X} (m : F ⟶ G) [Mono m]
    (U : Opens X) (g : G.obj.obj (op U))
    {I : Type u} (V : I → Opens X) (hVU : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i)
    (s : ∀ i, F.obj.obj (op (V i)))
    (hs : ∀ i, m.hom.app (op (V i)) (s i) =
      G.obj.map (homOfLE (hVU i)).op g) :
    ∃ t : F.obj.obj (op U), m.hom.app (op U) t = g := by
  have hinj := (SheafInjectiveSurjective.sheaf_mono_iff_injective m).1 inferInstance
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V s := by
    intro i j
    apply hinj (op (V i ⊓ V j))
    let W := V i ⊓ V j
    have hni : m.hom.app (op W) (F.obj.map (Opens.infLELeft (V i) (V j)).op (s i)) =
        G.obj.map (Opens.infLELeft (V i) (V j)).op
          (m.hom.app (op (V i)) (s i)) :=
      congrArg (fun q => q (s i)) (m.hom.naturality (Opens.infLELeft (V i) (V j)).op)
    have hnj : m.hom.app (op W) (F.obj.map (Opens.infLERight (V i) (V j)).op (s j)) =
        G.obj.map (Opens.infLERight (V i) (V j)).op
          (m.hom.app (op (V j)) (s j)) :=
      congrArg (fun q => q (s j)) (m.hom.naturality (Opens.infLERight (V i) (V j)).op)
    rw [hni, hnj, hs i, hs j]
    simp only [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
    congr 1
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' V U
    (fun i => homOfLE (hVU i)) hcover s hcompat
  refine ⟨t, ?_⟩
  apply G.eq_of_locally_eq' V U (fun i => homOfLE (hVU i)) hcover
  intro i
  rw [← NatTrans.naturality_apply m.hom (homOfLE (hVU i)).op t, ht i, hs i]

/-- A section of the target of a monomorphism of sheaves of sets whose germ at every point of `U`
is in the image of the stalk map lifts over `U`. -/
private theorem section_lift_of_stalkwise_image {X : TopCat.{u}}
    {F G : TopCat.Sheaf (Type u) X} (m : F ⟶ G) [Mono m]
    (U : Opens X) (g : G.obj.obj (op U))
    (h : ∀ (x : X) (hx : x ∈ U), ∃ a : F.presheaf.stalk x,
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map m.hom) a =
        G.presheaf.germ U x hx g) :
    ∃ t : F.obj.obj (op U), m.hom.app (op U) t = g := by
  let I := {x : X // x ∈ U}
  have hlocal (i : I) : ∃ (W : Opens X) (hWU : W ≤ U), i.1 ∈ W ∧
      ∃ s : F.obj.obj (op W), m.hom.app (op W) s =
        G.obj.map (homOfLE hWU).op g := by
    obtain ⟨a, ha⟩ := h i.1 i.2
    obtain ⟨V, hV, s, hs⟩ := F.presheaf.exists_germ_eq a
    have hgerm : G.presheaf.germ V i.1 hV (m.hom.app (op V) s) =
        G.presheaf.germ U i.1 i.2 g := by
      rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V i.1 hV m.hom s,
        hs, ha]
    obtain ⟨W, hW, jV, jU, heq⟩ := G.presheaf.germ_eq i.1 hV i.2
      (m.hom.app (op V) s) g hgerm
    refine ⟨W, jU.le, hW, F.obj.map jV.op s, ?_⟩
    exact (NatTrans.naturality_apply m.hom jV.op s).trans heq
  choose W hWU hxW s hs using hlocal
  exact section_lift_of_local_sections m U g W hWU
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩) s hs

/-- A global section of the target of a monomorphism of sheaves of sets whose germ at every point
of a subset `Z` meeting the closure of every point is in the image of the stalk map lifts
globally: the lift at a point is obtained by specialising from a point of `Z`. -/
private theorem section_lift_of_specialization_coverage {X : TopCat.{u}}
    {F G : TopCat.Sheaf (Type u) X} (m : F ⟶ G) [Mono m]
    (Z : Set X) (hcover : ∀ x : X, (Z ∩ closure ({x} : Set X)).Nonempty)
    (g : G.obj.obj (op ⊤))
    (hZ : ∀ z : Z, ∃ a : F.presheaf.stalk z.1,
      ((TopCat.Presheaf.stalkFunctor (Type u) z.1).map m.hom) a =
        G.presheaf.germ ⊤ z.1 (Set.mem_univ _) g) :
    ∃ f : F.obj.obj (op ⊤), m.hom.app (op ⊤) f = g := by
  apply section_lift_of_stalkwise_image m ⊤ g
  intro x hx
  obtain ⟨z, hzZ, hzx⟩ := hcover x
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hzx
  obtain ⟨a, ha⟩ := hZ ⟨z, hzZ⟩
  refine ⟨F.presheaf.stalkSpecializes hsp a, ?_⟩
  exact (congrArg (fun q => q a) (F.presheaf.stalkSpecializes_stalkFunctor_map m.hom hsp)).trans
    ((congrArg (fun q => G.presheaf.stalkSpecializes hsp q) ha).trans
      (congrArg (fun q => q g) (G.presheaf.germ_stalkSpecializes (U := ⊤) (Set.mem_univ z) hsp)))

/-! ### The restriction map on global sections -/

/-- The canonical map from global sections of `F` on `X` to global sections of its restriction
to the subspace `Z`. -/
noncomputable def globalSectionsRestriction {X : Type u} [TopologicalSpace X]
    (Z : Set X) (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    F.obj.obj (op ⊤) → ((pullback00AF (TopCat.of X) Z).obj F).obj.obj (op ⊤) := by
  intro s
  exact ConcreteCategory.hom
    (((pullbackPushforwardAdj (TopCat.of X) Z).unit.app F).hom.app (op ⊤)) s

/-- The unit of the pullback–pushforward adjunction is natural in the sheaf. -/
private lemma pullback_unit_natural {X Y : TopCat.{u}} (f : Y ⟶ X)
    {F G : X.Sheaf (Type u)} (m : F ⟶ G) (V : Opens X)
    (s : F.obj.obj (op V)) :
    (((TopCat.Sheaf.pullback (Type u) f).map m).hom.app
      (op ((Opens.map f).obj V)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
        (op V)) s) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app
      (op V)) (m.hom.app (op V) s) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality m
  have h' := congrArg (fun q : F ⟶
      (TopCat.Sheaf.pushforward (Type u) f).obj
        ((TopCat.Sheaf.pullback (Type u) f).obj G) => q.hom.app (op V) s) h
  change
    (m.hom.app (op V) ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app (op V)) s =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app (op V) ≫
      ((TopCat.Sheaf.pullback (Type u) f).map m).hom.app
        (op ((Opens.map f).obj V))) s at h'
  dsimp [TopCat.Sheaf.pushforward, Functor.sheafPushforwardContinuous,
    TopCat.Presheaf.pushforward] at h'
  exact h'.symm

/-- Restriction to a subspace is natural in the sheaf. -/
private lemma globalSectionsRestriction_natural {X : Type u} [TopologicalSpace X]
    (Z : Set X) {F G : TopCat.Sheaf (Type u) (TopCat.of X)}
    (m : F ⟶ G) (s : F.obj.obj (op ⊤)) :
    globalSectionsRestriction Z G (m.hom.app (op ⊤) s) =
      (((pullback00AF (TopCat.of X) Z).map m).hom.app (op ⊤))
        (globalSectionsRestriction Z F s) :=
  (pullback_unit_natural (Stacks.subsetInclusion (TopCat.of X) Z) m ⊤ s).symm

/-- `Stacks.globalSectionsRestriction` as a natural transformation from global sections on `X` to
global sections on `Z` of the restriction. -/
private noncomputable def globalSectionsRestrictionNat {X : Type u} [TopologicalSpace X]
    (Z : Set X) :
    (sheafSections (Opens.grothendieckTopology (TopCat.of X)) (Type u)).obj (op ⊤) ⟶
      (pullback00AF (TopCat.of X) Z) ⋙
        (sheafSections (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).obj (op ⊤) := by
  refine ⟨fun F => ↾(globalSectionsRestriction Z F), ?_⟩
  intro F G m
  ext s
  exact globalSectionsRestriction_natural Z m s

/-! ### Comparing the models of the sheaf pullback -/

/-- The identification of the stalks of a pullback sheaf is natural in the sheaf. -/
private theorem stalkPullbackSheafIso_natural {X Y : TopCat.{u}} (f : Y ⟶ X)
    {F G : X.Sheaf (Type u)} (m : F ⟶ G) (y : Y)
    (a : ((TopCat.Sheaf.pullback (Type u) f).obj F).presheaf.stalk y) :
    (stalkPullbackSheafIso f G y).hom
      (((TopCat.Presheaf.stalkFunctor (Type u) y).map
        ((TopCat.Sheaf.pullback (Type u) f).map m).hom) a) =
    ((TopCat.Presheaf.stalkFunctor (Type u) (f y)).map m.hom)
      ((stalkPullbackSheafIso f F y).hom a) := by
  obtain ⟨V, hV, s, hs⟩ := F.presheaf.exists_germ_eq
    ((stalkPullbackSheafIso f F y).hom a)
  let W := (Opens.map f).obj V
  have hyW : y ∈ W := hV
  let tF := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
    (op V) s
  have hrep : a = ((TopCat.Sheaf.pullback (Type u) f).obj F).presheaf.germ
      W y hyW tF := by
    have h := stalkPullbackSheafIso_inv_germ f F y V hV s
    rw [hs] at h
    simpa [tF, W] using h
  rw [hrep]
  have hG := stalkPullbackSheafIso_inv_germ f G y V hV (m.hom.app (op V) s)
  have hF := stalkPullbackSheafIso_inv_germ f F y V hV s
  have hFm := TopCat.Presheaf.stalkFunctor_map_germ_apply V (f y) hV m.hom s
  have hunit := pullback_unit_natural f m V s
  have hFhom : (stalkPullbackSheafIso f F y).hom
      (((TopCat.Sheaf.pullback (Type u) f).obj F).presheaf.germ W y hyW tF) =
      F.presheaf.germ V (f y) hV s := by
    have h := congrArg (stalkPullbackSheafIso f F y).hom hF
    simpa [W, tF] using h.symm
  have hGhom : (stalkPullbackSheafIso f G y).hom
      (((TopCat.Sheaf.pullback (Type u) f).obj G).presheaf.germ W y hyW
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app
          (op V) (m.hom.app (op V) s))) =
      G.presheaf.germ V (f y) hV (m.hom.app (op V) s) := by
    have h := congrArg (stalkPullbackSheafIso f G y).hom hG
    simpa [W] using h.symm
  have hgerm := congrArg (stalkPullbackSheafIso f G y).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hyW
      ((TopCat.Sheaf.pullback (Type u) f).map m).hom tF)
  have hstep := congrArg (fun q => (stalkPullbackSheafIso f G y).hom
    (((TopCat.Sheaf.pullback (Type u) f).obj G).presheaf.germ W y hyW q)) hunit
  exact hgerm.trans (hstep.trans (hGhom.trans (hFm.symm.trans
    (congrArg ((TopCat.Presheaf.stalkFunctor (Type u) (f y)).map m.hom) hFhom.symm))))

/-- The germ at a point `z` of `Z` of the restriction of a global section is the germ of the
section at `z`, under the identification of the stalks of a pullback sheaf. -/
private lemma germ_pullback_globalSectionsRestriction {X : Type u} [TopologicalSpace X]
    (Z : Set X) (F : TopCat.Sheaf (Type u) (TopCat.of X)) (z : TopCat.of Z)
    (s : F.obj.obj (op ⊤)) :
    let i : TopCat.of Z ⟶ TopCat.of X :=
      Stacks.subsetInclusion (TopCat.of X) Z
    ConcreteCategory.hom
        (((pullback00AF (TopCat.of X) Z).obj F).presheaf.germ ⊤ z (Set.mem_univ z) ≫
          (stalkPullbackSheafIso i F z).hom)
    (globalSectionsRestriction Z F s) =
    ConcreteCategory.hom
        (F.presheaf.germ ⊤
          (ConcreteCategory.hom i z)
          (Set.mem_univ _)) s := by
  let i := Stacks.subsetInclusion (TopCat.of X) Z
  have h := stalkPullbackSheafIso_inv_germ i F z ⊤ (Set.mem_univ _) s
  change (stalkPullbackSheafIso i F z).inv
      (F.presheaf.germ ⊤ (i z) (Set.mem_univ _) s) =
      ((TopCat.Sheaf.pullback (Type u) i).obj F).presheaf.germ ⊤ z
        (Set.mem_univ _) (globalSectionsRestriction Z F s) at h
  change (stalkPullbackSheafIso i F z).hom
      (((TopCat.Sheaf.pullback (Type u) i).obj F).presheaf.germ ⊤ z
        (Set.mem_univ _) (globalSectionsRestriction Z F s)) =
      F.presheaf.germ ⊤ (i z) (Set.mem_univ _) s
  rw [← h]
  exact Iso.inv_hom_id_apply (stalkPullbackSheafIso i F z) _

/-- Global sections with the same restriction to `Z` have the same germ at every point of `Z`. -/
private lemma germ_eq_of_globalSectionsRestriction_eq {X : Type u} [TopologicalSpace X]
    (Z : Set X) (F : TopCat.Sheaf (Type u) (TopCat.of X)) (z : TopCat.of Z)
    (s t : F.obj.obj (op ⊤))
    (h : globalSectionsRestriction Z F s = globalSectionsRestriction Z F t) :
    ConcreteCategory.hom (F.presheaf.germ ⊤
      (ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) Z) z) (Set.mem_univ _)) s =
    ConcreteCategory.hom (F.presheaf.germ ⊤
      (ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) Z) z) (Set.mem_univ _)) t := by
  rw [← germ_pullback_globalSectionsRestriction Z F z s,
    ← germ_pullback_globalSectionsRestriction Z F z t, h]

/-! ### Restriction commutes with filtered colimits and finite products -/

/-- A natural transformation between functors to sets that is surjective on every object of a
diagram is surjective at the vertex of a cocone whose image is a colimit. -/
private theorem surjective_natTrans_of_colimit
    {J : Type u} {C : Type (u + 1)} [SmallCategory J] [Category C]
    (D : J ⥤ C) (c : Cocone D) (A B : C ⥤ Type u) (η : A ⟶ B)
    (hB : IsColimit (B.mapCocone c))
    (hstage : ∀ j, Function.Surjective (η.app (D.obj j))) :
    Function.Surjective (η.app c.pt) := by
  intro y
  obtain ⟨j, yj, hy⟩ := Types.jointly_surjective_of_isColimit hB y
  obtain ⟨xj, hxj⟩ := hstage j yj
  exact ⟨(A.mapCocone c).ι.app j xj, (NatTrans.naturality_apply η (c.ι.app j) xj).trans
    ((congrArg (fun z => (B.mapCocone c).ι.app j z) hxj).trans hy)⟩

/-- If restriction to a closed subset `Z` of a spectral space is surjective on global sections of
every piece of a filtered diagram, it is surjective on global sections of the colimit: both
restriction and global sections on `Z` preserve the colimit. -/
private theorem surjective_restriction_of_filteredColimit
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ TopCat.Sheaf (Type u) (TopCat.of X))
    (c : Cocone D) (hc : IsColimit c)
    (hstage : ∀ j, Function.Surjective (globalSectionsRestriction Z (D.obj j))) :
    Function.Surjective (globalSectionsRestriction Z c.pt) := by
  let P := pullback00AF (TopCat.of X) Z
  let ΓZ := (sheafSections (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).obj (op ⊤)
  have : PreservesColimit D P := by
    let : P.IsLeftAdjoint := (pullbackPushforwardAdj (TopCat.of X) Z).isLeftAdjoint
    infer_instance
  let : SpectralSpace Z := spectralSpace_closed_subtype Z hZ
  have hΓ : PreservesColimit (D ⋙ P) ΓZ :=
    globalSections_preservesFilteredColimit (D ⋙ P)
      (top_hasFiniteCompactCofinalCovers (X := Z))
  have hB : IsColimit ((P ⋙ ΓZ).mapCocone c) :=
    (hΓ.preserves (isColimitOfPreserves P hc)).some.ofIsoColimit
      (Functor.mapCoconeMapCocone c)
  exact surjective_natTrans_of_colimit D c
    ((sheafSections (Opens.grothendieckTopology (TopCat.of X)) (Type u)).obj (op ⊤))
    (P ⋙ ΓZ) (globalSectionsRestrictionNat Z)
      hB hstage

/-- Restriction to a subspace is compatible with the identification of the global sections of a
finite product of sheaves with the product of their global sections. -/
private lemma globalSectionsRestriction_product {X : Type u} [TopologicalSpace X]
    (Z : Set X) (n : ℕ) (G : Fin n → TopCat.Sheaf (Type u) (TopCat.of X))
    [HasProduct G] (s : (∏ᶜ G).obj.obj (op ⊤)) (j : Fin n) :
    (pullbackProductSectionsEquiv (Stacks.subsetInclusion (TopCat.of X) Z) n G
      (globalSectionsRestriction Z (∏ᶜ G) s)) j =
    globalSectionsRestriction Z (G j) ((globalSectionsProductEquiv (TopCat.of X) G s) j) := by
  refine (pullbackProductSectionsEquiv_apply (Stacks.subsetInclusion (TopCat.of X) Z) n G
    (globalSectionsRestriction Z (∏ᶜ G) s) j).trans ?_
  exact (globalSectionsRestriction_natural Z (Pi.π G j) s).symm.trans
    (congrArg (globalSectionsRestriction Z (G j))
      (globalSectionsProductEquiv_apply (TopCat.of X) G s j).symm)

/-- If restriction to `Z` is surjective on global sections of each factor of a finite product of
sheaves, it is surjective on global sections of the product. -/
private theorem surjective_restriction_product {X : Type u} [TopologicalSpace X]
    (Z : Set X) (n : ℕ) (G : Fin n → TopCat.Sheaf (Type u) (TopCat.of X))
    [HasProduct G] (hG : ∀ j, Function.Surjective (globalSectionsRestriction Z (G j))) :
    Function.Surjective (globalSectionsRestriction Z (∏ᶜ G)) := by
  intro t
  let eX := globalSectionsProductEquiv (TopCat.of X) G
  let eZ := pullbackProductSectionsEquiv (Stacks.subsetInclusion (TopCat.of X) Z) n G
  choose s hs using fun j => hG j (eZ t j)
  refine ⟨eX.symm s, ?_⟩
  apply eZ.injective
  funext j
  refine (globalSectionsRestriction_product Z n G (eX.symm s) j).trans ?_
  rw [show (globalSectionsProductEquiv (TopCat.of X) G) (eX.symm s) = s from
    eX.apply_symm_apply s]
  exact hs j

/-! ### Restriction of the pushforward of a constant sheaf from a closed subset -/

/-- Restriction of a sheaf pushed forward from a closed subset `Y` to the trace of `Y` on `Z` is
injective on global sections: the stalks away from `Y` are singletons, and at a point of `Y ∩ Z`
the germ is determined by the restriction. -/
private theorem restriction_injective_of_closed_pushforward
    {X : Type u} [TopologicalSpace X]
    (Y Z : Set X) (hY : IsClosed Y)
    (C : TopCat.Sheaf (Type u) (TopCat.of Y)) :
    let G := (pushforward00AF (TopCat.of X) Y).obj C
    let H := (pullback00AF (TopCat.of X) Z).obj G
    let W : Set Z := {z | (z : X) ∈ Y}
    Function.Injective (globalSectionsRestriction W H) := by
  dsimp only
  let G := (pushforward00AF (TopCat.of X) Y).obj C
  let H := (pullback00AF (TopCat.of X) Z).obj G
  let W : Set Z := {z | (z : X) ∈ Y}
  intro s t hst
  apply TopCat.Presheaf.section_ext H ⊤
  intro z _
  by_cases hzY : (z : X) ∈ Y
  · let w : W := ⟨z, hzY⟩
    exact germ_eq_of_globalSectionsRestriction_eq W H w s t hst
  · obtain ⟨hu⟩ := pushforward_stalkIsSingleton_of_notMem
      (TopCat.of X) hY C z hzY
    let i := Stacks.subsetInclusion (TopCat.of X) Z
    let : Unique (G.presheaf.stalk (i z)) := hu
    let : Unique (H.presheaf.stalk z) :=
      Equiv.unique (stalkPullbackSheafIso i G z).toEquiv
    exact Subsingleton.elim _ _

/-- The inclusion of the trace of `Y` on `Z` into `Y`. -/
private def intersectionToY {X : Type u} [TopologicalSpace X]
    (Y Z : Set X) :
    TopCat.of {z : Z | (z : X) ∈ Y} ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun z => ⟨z.1.1, z.2⟩,
    Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)⟩

/-- The square formed by `Y`, `Z`, their trace and the ambient space commutes. -/
private theorem intersection_square {X : Type u} [TopologicalSpace X]
    (Y Z : Set X) :
    intersectionToY Y Z ≫ Stacks.subsetInclusion (TopCat.of X) Y =
      Stacks.subsetInclusion (TopCat.of Z) {z : Z | (z : X) ∈ Y} ≫
        Stacks.subsetInclusion (TopCat.of X) Z := by
  apply TopCat.Hom.ext
  ext z
  rfl

/-- The identification of the pullback along a composite with the composite of the pullbacks
carries the unit of the composite adjunction to the composite of the units, on global
sections. -/
private lemma sheafPullbackCompIso_global_unit {X Y Z : TopCat.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (s : F.obj.obj (op ⊤)) :
    ((sheafPullbackCompIso g f (Type u)).app F).hom.hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (g ≫ f)).unit.app F).hom.app
        (op ⊤) s) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app
      ((TopCat.Sheaf.pullback (Type u) f).obj F)).hom.app (op ⊤))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app
        (op ⊤) s) := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (g ≫ f)
  let b := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g)).ofNatIsoRight
      (sheafPushforwardCompIso g f (Type u)).symm
  calc
    _ = (a.unit.app F ≫ (TopCat.Sheaf.pushforward (Type u) (g ≫ f)).map
        ((a.leftAdjointUniq b).hom.app F)).hom.app (op ⊤) s := rfl
    _ = (b.unit.app F).hom.app (op ⊤) s :=
      congrArg (fun q => q.hom.app (op ⊤) s) (a.unit_leftAdjointUniq_hom_app b F)
    _ = _ := by
      simp only [b, sheafPushforwardCompIso]
      rfl

/-- Restricting to `Z` a sheaf pushed forward from a closed subset `Y`, and then restricting to
the trace of `Y` on `Z`, recovers the pullback of the original sheaf along the inclusion of the
trace into `Y`. -/
private noncomputable def intersectionPullbackPushforwardIso
    {X : Type u} [TopologicalSpace X] (Y Z : Set X)
    (C : TopCat.Sheaf (Type u) (TopCat.of Y)) :
    let G := (pushforward00AF (TopCat.of X) Y).obj C
    let H := (pullback00AF (TopCat.of X) Z).obj G
    let W : Set Z := {z | (z : X) ∈ Y}
    (pullback00AF (TopCat.of Z) W).obj H ≅
      (TopCat.Sheaf.pullback (Type u) (intersectionToY Y Z)).obj C := by
  let j := Stacks.subsetInclusion (TopCat.of X) Y
  let i := Stacks.subsetInclusion (TopCat.of X) Z
  let W : Set Z := {z | (z : X) ∈ Y}
  let k := Stacks.subsetInclusion (TopCat.of Z) W
  let p := intersectionToY Y Z
  let G := (TopCat.Sheaf.pushforward (Type u) j).obj C
  have hcomp : k ≫ i = p ≫ j := (intersection_square Y Z).symm
  let : (TopCat.Sheaf.pushforward (Type u) j).Full :=
    (pushforwardFullyFaithful (TopCat.of X) Y).full
  let : (TopCat.Sheaf.pushforward (Type u) j).Faithful :=
    (pushforwardFullyFaithful (TopCat.of X) Y).faithful
  exact ((sheafPullbackCompIso k i (Type u)).app G).symm ≪≫
    eqToIso (congrArg (fun f => (TopCat.Sheaf.pullback (Type u) f).obj G) hcomp) ≪≫
    (sheafPullbackCompIso p j (Type u)).app G ≪≫
    (TopCat.Sheaf.pullback (Type u) p).mapIso
      (asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) j).counit.app C))

/-- On global sections, `Stacks.intersectionPullbackPushforwardIso` carries the twofold
restriction of the canonical section to the canonical section. -/
private lemma intersectionPullbackPushforwardIso_global_unit
    {X : Type u} [TopologicalSpace X] (Y Z : Set X)
    (C : TopCat.Sheaf (Type u) (TopCat.of Y))
    (s : C.obj.obj (op ⊤)) :
    let G := (pushforward00AF (TopCat.of X) Y).obj C
    let H := (pullback00AF (TopCat.of X) Z).obj G
    let W : Set Z := {z | (z : X) ∈ Y}
    ((intersectionPullbackPushforwardIso Y Z C).hom.hom.app (op ⊤))
      (globalSectionsRestriction W H (globalSectionsRestriction Z G s)) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
      (intersectionToY Y Z)).unit.app C).hom.app (op ⊤)) s := by
  let j := Stacks.subsetInclusion (TopCat.of X) Y
  let i := Stacks.subsetInclusion (TopCat.of X) Z
  let W : Set Z := {z | (z : X) ∈ Y}
  let k := Stacks.subsetInclusion (TopCat.of Z) W
  let p := intersectionToY Y Z
  let G := (TopCat.Sheaf.pushforward (Type u) j).obj C
  let : (TopCat.Sheaf.pushforward (Type u) j).Full :=
    (pushforwardFullyFaithful (TopCat.of X) Y).full
  let : (TopCat.Sheaf.pushforward (Type u) j).Faithful :=
    (pushforwardFullyFaithful (TopCat.of X) Y).faithful
  have hcomp : k ≫ i = p ≫ j := (intersection_square Y Z).symm
  let α := (sheafPullbackCompIso k i (Type u)).app G
  let β := (sheafPullbackCompIso p j (Type u)).app G
  let E := eqToIso (congrArg (fun f => (TopCat.Sheaf.pullback (Type u) f).obj G) hcomp)
  let γ := (TopCat.Sheaf.pullback (Type u) p).mapIso
    (asIso ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) j).counit.app C))
  have hki := sheafPullbackCompIso_global_unit i k G s
  have hpj := sheafPullbackCompIso_global_unit j p G s
  have ha : α.inv.hom.app (op ⊤)
      (globalSectionsRestriction W ((TopCat.Sheaf.pullback (Type u) i).obj G)
        (globalSectionsRestriction Z G s)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (k ≫ i)).unit.app G).hom.app
        (op ⊤) s := by
    change α.inv.hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) k).unit.app
        ((TopCat.Sheaf.pullback (Type u) i).obj G)).hom.app (op ⊤)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G).hom.app
          (op ⊤) s)) = _
    rw [← hki]
    exact congrArg (fun q => q.hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (k ≫ i)).unit.app G).hom.app
        (op ⊤) s)) α.hom_inv_id
  change γ.hom.hom.app (op ⊤)
    (β.hom.hom.app (op ⊤)
      (E.hom.hom.app (op ⊤)
        (α.inv.hom.app (op ⊤)
          (globalSectionsRestriction W ((TopCat.Sheaf.pullback (Type u) i).obj G)
            (globalSectionsRestriction Z G s))))) = _
  rw [ha]
  have he : E.hom.hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (k ≫ i)).unit.app G).hom.app
        (op ⊤) s) =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (p ≫ j)).unit.app G).hom.app
        (op ⊤) s) := by
    cases hcomp
    rfl
  rw [he, hpj]
  let aj := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) j
  let u := (aj.unit.app G).hom.app (op ⊤) s
  have hn := pullback_unit_natural p (aj.counit.app C) ⊤ u
  have ht := congrArg (fun q => q.hom.app (op ⊤) s) (aj.right_triangle_components C)
  change (aj.counit.app C).hom.app (op ⊤)
      ((aj.unit.app G).hom.app (op ⊤) s) = s at ht
  change γ.hom.hom.app (op ⊤)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) p).unit.app
      ((TopCat.Sheaf.pullback (Type u) j).obj G)).hom.app (op ⊤) u) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) p).unit.app C).hom.app
        (op ⊤) s
  exact hn.trans (congrArg _ ht)

/-- A locally constant function on the trace of a closed subset `Y` on `Z` extends to a locally
constant function on `Y`: `Y` is again spectral and its trace on `Z` again meets the closure of
every point of `Y` in a connected set. -/
private lemma exists_locallyConstant_extension_intersection
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (Y Z : Set X) (hY : IsClosed Y) (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (S : Type u)
    (f : {z : Z | (z : X) ∈ Y} → S) (hf : IsLocallyConstant f) :
    ∃ g : Y → S, IsLocallyConstant g ∧
      ∀ w : {z : Z | (z : X) ∈ Y}, g (intersectionToY Y Z w) = f w := by
  let : SpectralSpace Y := spectralSpace_closed_subtype Y hY
  let T : Set Y := {y | (y : X) ∈ Z}
  have hT : IsClosed T := hZ.preimage continuous_subtype_val
  have hconnY : ∀ y : Y, IsConnected (T ∩ closure ({y} : Set Y)) :=
    isConnected_inter_closure_closed_subtype hY hconn
  let φ : T → {z : Z | (z : X) ∈ Y} :=
    fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk
      (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2))
      (fun y => y.1.2)
  obtain ⟨g, hg, hgt⟩ := exists_isLocallyConstant_extension T hT hconnY
    (f ∘ φ) (hf.comp_continuous hφ)
  exact ⟨g, hg, fun w => hgt ⟨⟨w.1.1, w.2⟩, w.1.2⟩⟩

/-- The constant sheaf on `X` is the pullback of the constant sheaf on `Y` along `f`, and the
comparison carries a `Stacks.globalConstantSection` to the `Stacks.globalConstantSection` with the
same value. -/
private lemma constantSheafPullbackIso_globalConstantSection
    {X Y : TopCat.{u}} (f : X ⟶ Y) (S : Type u) (a : S) :
    ((constantSheafPullbackIso f).app S).hom.hom.app (op ⊤)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
        (constantSheafOnSpace Y (Type u) S)).hom.app (op ⊤)
          (globalConstantSection Y S a)) =
    globalConstantSection X S a := by
  let adj₁ := (constantSheafAdj (Opens.grothendieckTopology Y) (Type u)
    (isTerminalTop (α := Opens Y))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
  let adj₂ := constantSheafAdj (Opens.grothendieckTopology X) (Type u)
    (isTerminalTop (α := Opens X))
  exact congrArg (fun q => q a) (adj₁.unit_leftAdjointUniq_hom_app adj₂ S)

/-- Restricting a global section of a constant sheaf along `f` composes the underlying locally
constant function with `f`. -/
private lemma constantSheafPullbackIso_locallyConstant
    {X Y : TopCat.{u}} (f : X ⟶ Y) (S : Type u)
    (s : (constantSheafOnSpace Y (Type u) S).obj.obj (op ⊤)) (x : X) :
    locallyConstantOfConstantSection X S
      (((constantSheafPullbackIso f).app S).hom.hom.app (op ⊤)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
          (constantSheafOnSpace Y (Type u) S)).hom.app (op ⊤) s)) x =
    locallyConstantOfConstantSection Y S s (f x) := by
  let F : Y.Sheaf (Type u) := constantSheafOnSpace Y (Type u) S
  let H := (TopCat.Sheaf.pullback (Type u) f).obj F
  let K : X.Sheaf (Type u) := constantSheafOnSpace X (Type u) S
  let e := (constantSheafPullbackIso f).app S
  let r := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom.app (op ⊤)
  obtain ⟨a, ha⟩ := exists_globalConstantSection_germ_eq Y S s (f x)
  have hY := locallyConstantOfConstantSection_eq_of_germ Y S (f x) s
    (globalConstantSection Y S a) ha
  have hres : H.presheaf.germ ⊤ x (Set.mem_univ x) (r s) =
      H.presheaf.germ ⊤ x (Set.mem_univ x) (r (globalConstantSection Y S a)) :=
    (stalkPullbackSheafIso_inv_germ f F x ⊤ (Set.mem_univ _) s).symm.trans
      ((congrArg (stalkPullbackSheafIso f F x).inv ha).trans
        (stalkPullbackSheafIso_inv_germ f F x ⊤ (Set.mem_univ _)
          (globalConstantSection Y S a)))
  have hmap := congrArg
    (fun q => ((TopCat.Presheaf.stalkFunctor (Type u) x).map e.hom.hom) q) hres
  have hm1 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Set.mem_univ x)
    e.hom.hom (r s)
  have hm2 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x (Set.mem_univ x)
    e.hom.hom (r (globalConstantSection Y S a))
  change ((TopCat.Presheaf.stalkFunctor (Type u) x).map e.hom.hom)
    (H.presheaf.germ ⊤ x (Set.mem_univ x) (r s)) =
    K.presheaf.germ ⊤ x (Set.mem_univ x) (e.hom.hom.app (op ⊤) (r s)) at hm1
  change ((TopCat.Presheaf.stalkFunctor (Type u) x).map e.hom.hom)
    (H.presheaf.germ ⊤ x (Set.mem_univ x) (r (globalConstantSection Y S a))) =
    K.presheaf.germ ⊤ x (Set.mem_univ x)
      (e.hom.hom.app (op ⊤) (r (globalConstantSection Y S a))) at hm2
  rw [hm1, hm2] at hmap
  have hc := constantSheafPullbackIso_globalConstantSection f S a
  rw [hc] at hmap
  have hX := locallyConstantOfConstantSection_eq_of_germ X S x
    (e.hom.hom.app (op ⊤) (r s)) (globalConstantSection X S a) hmap
  rw [locallyConstantOfConstantSection_globalConstantSection] at hX hY
  exact hX.trans hY.symm

/-- Restriction to `Z` is surjective on global sections of the pushforward of a constant sheaf
from a closed subset `Y`: a global section restricted to `Z` is a locally constant function on the
trace of `Y` on `Z`, which extends to `Y` by
`Stacks.exists_locallyConstant_extension_intersection`. -/
private theorem surjective_restriction_closedConstantPushforward
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (Y Z : Set X) (hY : IsClosed Y) (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (S : Type u) :
    Function.Surjective (globalSectionsRestriction Z
      (constantSheafPushforward Y S)) := by
  let C : TopCat.Sheaf (Type u) (TopCat.of Y) :=
    constantSheafOnSpace (TopCat.of Y) (Type u) S
  let G := (pushforward00AF (TopCat.of X) Y).obj C
  let H := (pullback00AF (TopCat.of X) Z).obj G
  let W : Set Z := {z | (z : X) ∈ Y}
  let p := intersectionToY Y Z
  let q := intersectionPullbackPushforwardIso Y Z C
  let e := (constantSheafPullbackIso p).app S
  intro t
  let u := q.hom.hom.app (op ⊤) (globalSectionsRestriction W H t)
  let v := e.hom.hom.app (op ⊤) u
  let f := locallyConstantOfConstantSection (TopCat.of W) S v
  obtain ⟨g, hg, hgw⟩ := exists_locallyConstant_extension_intersection Y Z hY hZ
    hconn S f f.isLocallyConstant
  let gLC : LocallyConstant Y S := ⟨g, hg⟩
  let sY := constantSectionOfLocallyConstant (TopCat.of Y) S gLC
  let r := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) p).unit.app C).hom.app
    (op ⊤) sY
  have hloc : locallyConstantOfConstantSection (TopCat.of W) S
      (e.hom.hom.app (op ⊤) r) = f := by
    ext w
    rw [constantSheafPullbackIso_locallyConstant,
      locallyConstantOfConstantSection_sectionOf]
    exact hgw w
  have he : r = u :=
    (((sheafSections (Opens.grothendieckTopology (TopCat.of W)) (Type u)).obj
      (op ⊤)).mapIso e).toEquiv.injective
        ((constantSectionsEquivLocallyConstant (TopCat.of W) S).injective hloc)
  have hW : globalSectionsRestriction W H (globalSectionsRestriction Z G sY) =
      globalSectionsRestriction W H t :=
    (((sheafSections (Opens.grothendieckTopology (TopCat.of W)) (Type u)).obj
      (op ⊤)).mapIso q).toEquiv.injective
        ((intersectionPullbackPushforwardIso_global_unit Y Z C sY).trans he)
  exact ⟨sY, restriction_injective_of_closed_pushforward Y Z hY C hW⟩

/-! ### Surjectivity of the restriction map -/

/-- Pullback of sheaves of sets preserves monomorphisms, because it preserves finite limits. -/
private theorem mono_pullback {X Y : TopCat.{u}} (i : Y ⟶ X)
    {F G : X.Sheaf (Type u)} (m : F ⟶ G) [Mono m] :
    Mono ((TopCat.Sheaf.pullback (Type u) i).map m) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.pullback (Type u) i) :=
    pullbackPreservesFiniteLimits i
  exact Functor.map_mono _ m

/-- If restriction to `Z` is surjective on global sections of `G` and `F` is a subsheaf of `G`,
then restriction to `Z` is surjective on global sections of `F`: a global section of `G` whose
restriction to `Z` comes from `F` has all its germs in `F`, because every point of `X` specialises
to a point of `Z`. -/
private theorem surjective_restriction_of_mono
    {X : Type u} [TopologicalSpace X]
    (Z : Set X) (hcover : ∀ x : X, (Z ∩ closure ({x} : Set X)).Nonempty)
    {F G : TopCat.Sheaf (Type u) (TopCat.of X)} (m : F ⟶ G) [Mono m]
    (hG : Function.Surjective (globalSectionsRestriction Z G)) :
    Function.Surjective (globalSectionsRestriction Z F) := by
  intro t
  let i := Stacks.subsetInclusion (TopCat.of X) Z
  let mZ := (TopCat.Sheaf.pullback (Type u) i).map m
  let tG := mZ.hom.app (op ⊤) t
  obtain ⟨g, hg⟩ := hG tG
  have hfactor : ∀ z : Z, ∃ a : F.presheaf.stalk z.1,
      ((TopCat.Presheaf.stalkFunctor (Type u) z.1).map m.hom) a =
        G.presheaf.germ ⊤ z.1 (Set.mem_univ _) g := by
    intro z
    let a := (stalkPullbackSheafIso i F z).hom
      (((TopCat.Sheaf.pullback (Type u) i).obj F).presheaf.germ ⊤ z (Set.mem_univ _) t)
    refine ⟨a, ?_⟩
    have hn := stalkPullbackSheafIso_natural i m z
      (((TopCat.Sheaf.pullback (Type u) i).obj F).presheaf.germ ⊤ z (Set.mem_univ _) t)
    have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ z (Set.mem_univ _)
      mZ.hom t
    have hres := germ_pullback_globalSectionsRestriction Z G z g
    have hstep : (stalkPullbackSheafIso i G z).hom
        (((TopCat.Sheaf.pullback (Type u) i).obj G).presheaf.germ ⊤ z
          (Set.mem_univ _) tG) =
        (stalkPullbackSheafIso i G z).hom
        (((TopCat.Sheaf.pullback (Type u) i).obj G).presheaf.germ ⊤ z
          (Set.mem_univ _) (globalSectionsRestriction Z G g)) := by
      rw [hg]
    exact hn.symm.trans ((congrArg (stalkPullbackSheafIso i G z).hom hmap).trans
      (hstep.trans hres))
  obtain ⟨f, hf⟩ := section_lift_of_specialization_coverage m Z hcover g hfactor
  refine ⟨f, ?_⟩
  have : Mono mZ := mono_pullback i m
  apply (SheafInjectiveSurjective.sheaf_mono_iff_injective mZ).1 inferInstance (op ⊤)
  have hunit := pullback_unit_natural i m ⊤ f
  change mZ.hom.app (op ⊤) (globalSectionsRestriction Z F f) = tG
  exact hunit.trans ((congrArg (globalSectionsRestriction Z G) hf).trans hg)

/-- Restriction to `Z` is surjective on global sections of a sheaf with a finite presentation by
finite constant sheaves on quasi-compact opens: such a sheaf embeds into a finite product of
pushforwards of finite constant sheaves from closed constructible subsets. -/
private theorem surjective_restriction_of_finitePresentation
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (Z : Set X) (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (F : TopCat.Sheaf (Type u) (TopCat.of X))
    (hF : HasFiniteBasisCoequalizerPresentation
      {U : Opens X | IsCompact (U : Set X)} F)
    (hconstant : ∀ (Y : Set X), IsClosed Y → Topology.IsConstructible Y →
      ∀ (S : Type u), Finite S →
        Function.Surjective (globalSectionsRestriction Z
          (constantSheafPushforward Y S))) :
    Function.Surjective (globalSectionsRestriction Z F) := by
  let : HasFiniteProducts (TopCat.Sheaf (Type u) (TopCat.of X)) :=
    CategoryTheory.Sheaf.instHasFiniteProducts
  obtain ⟨n, Y, hYclosed, hYconstructible, S, hS, m, hm⟩ :=
    exists_mono_to_pi_constantSheafPushforward F hF
  let : Mono m := hm
  exact surjective_restriction_of_mono Z (fun x => (hconn x).nonempty) m
    (surjective_restriction_product Z n (fun j => constantSheafPushforward (Y j) (S j))
      fun j => hconstant (Y j) (hYclosed j) (hYconstructible j) (S j) (hS j))

/-! ### The main theorem -/

/-- **Stacks Project, Tag 09ZG.** Let `Z` be a closed subset of a spectral space `X` meeting the
closure of every point of `X` in a connected set. Then restriction to `Z` is a bijection on global
sections of every sheaf of sets on `X`. -/
@[stacks 09ZG]
theorem bijective_globalSectionsRestriction_of_isConnected_inter_closure
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    Function.Bijective (globalSectionsRestriction Z F) := by
  refine ⟨?_, ?_⟩
  · intro s t hst
    apply TopCat.Presheaf.section_ext F ⊤
    intro x _
    obtain ⟨y, hy⟩ := (hconn x).nonempty
    have hstalk := germ_eq_of_globalSectionsRestriction_eq Z F (⟨y, hy.1⟩ : TopCat.of Z) s t hst
    have hsp : x ⤳ y := specializes_iff_mem_closure.mpr hy.2
    have hmap := congrArg (fun q => F.presheaf.stalkSpecializes hsp q) hstalk
    have hs := ConcreteCategory.congr_hom
      (F.presheaf.germ_stalkSpecializes (Set.mem_univ y) hsp) s
    have ht := ConcreteCategory.congr_hom
      (F.presheaf.germ_stalkSpecializes (Set.mem_univ y) hsp) t
    exact hs.symm.trans (hmap.trans ht)
  · obtain ⟨J, instJ, instFiltered, D, ι, hcolim, hstage⟩ :=
      isFilteredColimit_of_prespectralSpace F
    let : SmallCategory J := instJ
    let : IsFiltered J := instFiltered
    exact surjective_restriction_of_filteredColimit Z hZ D (Cocone.mk F ι) hcolim fun j =>
      surjective_restriction_of_finitePresentation Z hconn (D.obj j) (hstage j)
        fun Y hYclosed _ S _ =>
          surjective_restriction_closedConstantPushforward Y Z hYclosed hZ hconn S

end Stacks
