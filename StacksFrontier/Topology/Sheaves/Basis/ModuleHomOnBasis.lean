module

public import StacksFrontier.Topology.Sheaves.Basis.ModuleRestriction

/-!
# Morphisms of sheaves of modules from compatible maps on a basis

Let `X` be a topological space, `𝒪` a sheaf of rings on `X`, and let `F` and `G` be sheaves of
`𝒪`-modules. A morphism `F ⟶ G` is a family of `𝒪(U)`-linear maps on the sections over *every*
open `U`. This file records that it suffices to give such maps on the members of a basis of the
topology, compatibly with the restriction maps between them: the resulting morphism exists and is
unique.

Both halves come from Stacks 009U, `Stacks.BasisRestriction.isEquivalence_restrictModuleSheaf`:
the restriction functor to the basis is full, which produces the morphism, and faithful, which
makes it unique.

## Main results

* `Stacks.BasisRestriction.moduleSheafHom_ext_onBasis`: two morphisms of sheaves of modules that
  agree on the sections over every member of a basis are equal.
* `Stacks.BasisRestriction.moduleSheafHomOfBasisData`: the morphism of sheaves of modules
  constructed from a compatible family of maps on the sections over the members of a basis, and
  `Stacks.BasisRestriction.moduleSheafHomOfBasisData_app`, its components.
* `Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis`: the same when the basis is
  presented as the range of a family of opens.
* `Stacks.BasisRestriction.existsUnique_moduleSheafHom_of_sectionHom_onBasis`: that morphism is
  the unique one with the given components.
* `Stacks.BasisRestriction.moduleSheafSection_ext_of_cover`: two sections agreeing on a family of
  opens covering the open in question are equal, and
  `Stacks.BasisRestriction.moduleSheafSection_ext_onBasis`: two sections agreeing on a basis are
  equal.

## Implementation notes

The construction comes in two layers. `moduleSheafHomOfBasisData` takes the family indexed by
the members of the basis themselves and involves no choice: the restriction of a sheaf of modules
to the basis has exactly those sections and restriction maps, so the family *is* a morphism
there, and the construction is its lift along the restriction functor
`Stacks.BasisRestriction.restrictModuleSheaf_preimage`.

`moduleSheafHomOfSectionHomOnBasis` takes the family indexed by a family of opens `U : ι → Opens X`
whose range is the basis, which is the shape data usually comes in. Passing to the first layer
needs one index per member of the basis, and a member may be hit by several indices, so an index
is chosen (`Exists.choose` on the range membership). That choice is invisible in the result:
`basisIndexedMap_eq` shows the map attached to a member of the basis is the one attached to *any*
index hitting it, which is where the reflexive case of the compatibility hypothesis is used, and
`moduleSheafHomOfSectionHomOnBasis_app` is the component statement that follows.

## References

* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.BasisRestriction

universe u

attribute [local instance_reducible] TopCat.Sheaf
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat X}

/-- Transporting a map of sections along an equality of opens: the transported map is the one
determined by compatibility with the restriction along that equality. -/
theorem moduleSheafHom_transport (F G : SheafOfModules.{u} 𝒪) {A B : Opens X} (h : A = B)
    (eA : F.val.obj (op A) ⟶ G.val.obj (op A))
    (eB : F.val.obj (op B) ⟶ G.val.obj (op B))
    (hcomp : ∀ s, eB (F.val.map (homOfLE h.ge).op s) =
      G.val.map (homOfLE h.ge).op (eA s)) :
    h ▸ eA = eB := by
  cases h
  apply ModuleCat.hom_ext
  ext s
  simpa using (hcomp s).symm

/-- Compatibility of two maps of sections with a restriction is preserved by transporting both
along equalities of opens. -/
theorem moduleSheafHom_transport_naturality (F G : SheafOfModules.{u} 𝒪)
    {A B A' B' : Opens X} (hA : A = A') (hB : B = B')
    (eA : F.val.obj (op A) ⟶ G.val.obj (op A))
    (eB : F.val.obj (op B) ⟶ G.val.obj (op B)) (h : B ≤ A)
    (hcomp : ∀ s, eB (F.val.map (homOfLE h).op s) =
      G.val.map (homOfLE h).op (eA s))
    (h' : B' ≤ A') :
    ∀ s, (hB ▸ eB) (F.val.map (homOfLE h').op s) =
      G.val.map (homOfLE h').op ((hA ▸ eA) s) := by
  cases hA
  cases hB
  exact hcomp

/-- **Two sections of a sheaf of modules agreeing on a family of opens that covers the given open
are equal.** The family is not asked to be a basis of the space, only to lie inside the open and
to cover it. -/
theorem moduleSheafSection_ext_of_cover (F : SheafOfModules.{u} 𝒪)
    {ι : Type*} (U : ι → Opens X) {W : Opens X} (hle : ∀ a, U a ≤ W)
    (hcover : ∀ x ∈ W, ∃ a, x ∈ U a) (s t : F.val.obj (op W))
    (h : ∀ a, F.val.map (homOfLE (hle a)).op s = F.val.map (homOfLE (hle a)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf 𝒪).obj F) U W
    (fun a => homOfLE (hle a))
    (fun x hx => Opens.mem_iSup.mpr (hcover x hx)) s t h

/-- **Two sections of a sheaf of modules agreeing on a basis are equal.** -/
theorem moduleSheafSection_ext_onBasis (F : SheafOfModules.{u} 𝒪)
    {ι : Type*} (U : ι → Opens X) (hU : Opens.IsBasis (Set.range U))
    {W : Opens X} (s t : F.val.obj (op W))
    (h : ∀ (a : ι) (hle : U a ≤ W),
      F.val.map (homOfLE hle).op s = F.val.map (homOfLE hle).op t) :
    s = t := by
  refine moduleSheafSection_ext_of_cover F (fun p : {a : ι // U a ≤ W} => U p.1)
    (fun p => p.2) (fun x hx => ?_) s t fun p => h p.1 p.2
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hU hx
  obtain ⟨a, rfl⟩ := hV
  exact ⟨⟨a, hVW⟩, hxV⟩

/-- **Two morphisms of sheaves of modules agreeing on a basis are equal.** -/
theorem moduleSheafHom_ext_onBasis (F G : SheafOfModules.{u} 𝒪)
    {ι : Type*} (U : ι → Opens X) (hU : Opens.IsBasis (Set.range U))
    (E₁ E₂ : F ⟶ G) (h : ∀ a, E₁.val.app (op (U a)) = E₂.val.app (op (U a))) :
    E₁ = E₂ := by
  let : (restrictModuleSheaf hU 𝒪).Faithful := restrictModuleSheaf_faithful hU 𝒪
  apply (restrictModuleSheaf hU 𝒪).map_injective (a₁ := E₁) (a₂ := E₂)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  obtain ⟨a, ha⟩ := V.unop.property
  have hE := h a
  rw [ha] at hE
  exact hE

section Construction

variable (F G : SheafOfModules.{u} 𝒪) {B : Set (Opens X)} (hB : Opens.IsBasis B)
  (e : ∀ V : BasisCat B, F.val.obj (op V.obj) ⟶ G.val.obj (op V.obj))
  (hcomp : ∀ (V W : BasisCat B) (h : W.obj ≤ V.obj) (s : F.val.obj (op V.obj)),
    e W (F.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (e V s))

/-- The morphism of the restrictions to the basis determined by a compatible family of maps on
the sections over the members of the basis. -/
public noncomputable def basisDataHom :
    (restrictModuleSheaf hB 𝒪).obj F ⟶ (restrictModuleSheaf hB 𝒪).obj G :=
  ⟨{ app := fun V => e V.unop
     naturality := by
       intro V W hVW
       apply ModuleCat.hom_ext
       ext s
       exact hcomp V.unop W.unop hVW.unop.hom.le s }⟩

/-- **The morphism of sheaves of modules determined by a compatible family of maps on a
basis.** -/
public noncomputable def moduleSheafHomOfBasisData : F ⟶ G :=
  restrictModuleSheaf_preimage hB 𝒪 F G (basisDataHom F G hB e hcomp)

/-- The constructed morphism has the given map as its component on each member of the basis. -/
public theorem moduleSheafHomOfBasisData_app (V : BasisCat B) :
    (moduleSheafHomOfBasisData F G hB e hcomp).val.app (op V.obj) = e V :=
  congrArg (fun φ => φ.val.app (op V))
    (restrictModuleSheaf_preimage_spec hB 𝒪 F G (basisDataHom F G hB e hcomp))

end Construction

section OfFamily

variable (F G : SheafOfModules.{u} 𝒪) {ι : Type*} (U : ι → Opens X)
  (e : ∀ a, F.val.obj (op (U a)) ⟶ G.val.obj (op (U a)))

/-- The compatibility of a family of maps indexed by a family of opens. -/
public abbrev IsCompatibleOnBasis : Prop :=
  ∀ a b (h : U b ≤ U a) (s : F.val.obj (op (U a))),
    e b (F.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (e a s)

/-- The map attached to a member of the basis: the one attached to a chosen index hitting it,
transported along the equality of opens. -/
public noncomputable def basisIndexedMap (V : BasisCat (Set.range U)) :
    F.val.obj (op V.obj) ⟶ G.val.obj (op V.obj) :=
  V.property.choose_spec ▸ e V.property.choose

/-- The map attached to a member of the basis is the one attached to *any* index hitting it. -/
public theorem basisIndexedMap_eq (hcomp : IsCompatibleOnBasis F G U e)
    (V : BasisCat (Set.range U)) (i : ι) (hi : U i = V.obj) :
    basisIndexedMap F G U e V = hi ▸ e i :=
  moduleSheafHom_transport F G rfl (basisIndexedMap F G U e V) (hi ▸ e i)
    (moduleSheafHom_transport_naturality F G V.property.choose_spec hi
      (e V.property.choose) (e i) (V.property.choose_spec.trans hi.symm).ge
      (hcomp V.property.choose i _) le_rfl)

/-- The transported family is compatible with the restrictions between members of the basis. -/
public theorem basisIndexedMap_restrict (hcomp : IsCompatibleOnBasis F G U e)
    (V W : BasisCat (Set.range U)) (h : W.obj ≤ V.obj) (s : F.val.obj (op V.obj)) :
    basisIndexedMap F G U e W (F.val.map (homOfLE h).op s) =
      G.val.map (homOfLE h).op (basisIndexedMap F G U e V s) :=
  moduleSheafHom_transport_naturality F G V.property.choose_spec W.property.choose_spec
    (e V.property.choose) (e W.property.choose)
    (by rw [V.property.choose_spec, W.property.choose_spec]; exact h)
    (hcomp V.property.choose W.property.choose _) h s

/-- **The morphism of sheaves of modules glued from a compatible family of maps indexed by a
family of opens whose range is a basis.** -/
public noncomputable def moduleSheafHomOfSectionHomOnBasis
    (hU : Opens.IsBasis (Set.range U)) (hcomp : IsCompatibleOnBasis F G U e) : F ⟶ G :=
  moduleSheafHomOfBasisData F G hU (basisIndexedMap F G U e)
    (basisIndexedMap_restrict F G U e hcomp)

/-- The glued morphism has `e a` as its component on `U a`. -/
public theorem moduleSheafHomOfSectionHomOnBasis_app
    (hU : Opens.IsBasis (Set.range U)) (hcomp : IsCompatibleOnBasis F G U e) (a : ι) :
    (moduleSheafHomOfSectionHomOnBasis F G U e hU hcomp).val.app (op (U a)) = e a :=
  (moduleSheafHomOfBasisData_app F G hU (basisIndexedMap F G U e)
    (basisIndexedMap_restrict F G U e hcomp)
    (⟨U a, ⟨a, rfl⟩⟩ : BasisCat (Set.range U))).trans
      (basisIndexedMap_eq F G U e hcomp ⟨U a, ⟨a, rfl⟩⟩ a rfl)

/-- **A compatible family of maps on a basis extends to a unique morphism of sheaves of
modules.** Given a basis presented as the range of `U : ι → Opens X` and `𝒪(U a)`-linear maps
`e a` on the sections over each `U a` which commute with the restriction maps between the
`U a`, `moduleSheafHomOfSectionHomOnBasis` is the only morphism `F ⟶ G` whose component on
each `U a` is `e a`. -/
public theorem existsUnique_moduleSheafHom_of_sectionHom_onBasis
    (hU : Opens.IsBasis (Set.range U)) (hcomp : IsCompatibleOnBasis F G U e) :
    ∃! E : F ⟶ G, ∀ a, E.val.app (op (U a)) = e a :=
  ⟨moduleSheafHomOfSectionHomOnBasis F G U e hU hcomp,
    moduleSheafHomOfSectionHomOnBasis_app F G U e hU hcomp,
    fun E hE => moduleSheafHom_ext_onBasis F G U hU E _ fun a =>
      (hE a).trans (moduleSheafHomOfSectionHomOnBasis_app F G U e hU hcomp a).symm⟩

end OfFamily

section IsoOfFamily

variable (F G : SheafOfModules.{u} 𝒪) {ι : Type*} (U : ι → Opens X)
  (e : ∀ a, F.val.obj (op (U a)) ≅ G.val.obj (op (U a)))

/-- The inverses of a compatible family of isomorphisms on a basis are again compatible with the
restriction maps. -/
public theorem isCompatibleOnBasis_inv
    (hcomp : IsCompatibleOnBasis F G U fun a => (e a).hom) :
    IsCompatibleOnBasis G F U fun a => (e a).inv := by
  intro a b h s
  have hhi : ∀ z : F.val.obj (op (U b)), (e b).inv ((e b).hom z) = z := fun z =>
    congrArg (fun k : F.val.obj (op (U b)) ⟶ F.val.obj (op (U b)) => k z) (e b).hom_inv_id
  have hih : ∀ z : G.val.obj (op (U a)), (e a).hom ((e a).inv z) = z := fun z =>
    congrArg (fun k : G.val.obj (op (U a)) ⟶ G.val.obj (op (U a)) => k z) (e a).inv_hom_id
  have hkey := hcomp a b h ((e a).inv s)
  rw [hih s] at hkey
  exact (congrArg (fun z => (e b).inv z) hkey.symm).trans (hhi _)

/-- **A compatible family of isomorphisms on a basis assembles into an isomorphism of sheaves of
modules.** -/
public noncomputable def moduleSheafIsoOfSectionIsoOnBasis
    (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasis F G U fun a => (e a).hom) : F ≅ G where
  hom := moduleSheafHomOfSectionHomOnBasis F G U (fun a => (e a).hom) hU hcomp
  inv := moduleSheafHomOfSectionHomOnBasis G F U (fun a => (e a).inv) hU
    (isCompatibleOnBasis_inv F G U e hcomp)
  hom_inv_id := by
    refine moduleSheafHom_ext_onBasis F F U hU _ _ fun a => ?_
    change (moduleSheafHomOfSectionHomOnBasis F G U (fun a => (e a).hom) hU hcomp).val.app
        (op (U a)) ≫ (moduleSheafHomOfSectionHomOnBasis G F U (fun a => (e a).inv) hU
          (isCompatibleOnBasis_inv F G U e hcomp)).val.app (op (U a)) = 𝟙 _
    rw [moduleSheafHomOfSectionHomOnBasis_app, moduleSheafHomOfSectionHomOnBasis_app]
    exact (e a).hom_inv_id
  inv_hom_id := by
    refine moduleSheafHom_ext_onBasis G G U hU _ _ fun a => ?_
    change (moduleSheafHomOfSectionHomOnBasis G F U (fun a => (e a).inv) hU
          (isCompatibleOnBasis_inv F G U e hcomp)).val.app (op (U a)) ≫
        (moduleSheafHomOfSectionHomOnBasis F G U (fun a => (e a).hom) hU hcomp).val.app
          (op (U a)) = 𝟙 _
    rw [moduleSheafHomOfSectionHomOnBasis_app, moduleSheafHomOfSectionHomOnBasis_app]
    exact (e a).inv_hom_id

/-- The assembled isomorphism is the assembled morphism of the family of forward maps. -/
public theorem moduleSheafIsoOfSectionIsoOnBasis_hom
    (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasis F G U fun a => (e a).hom) :
    (moduleSheafIsoOfSectionIsoOnBasis F G U e hU hcomp).hom =
      moduleSheafHomOfSectionHomOnBasis F G U (fun a => (e a).hom) hU hcomp :=
  rfl

/-- The assembled isomorphism has `e a` as its component on `U a`. -/
public theorem moduleSheafIsoOfSectionIsoOnBasis_hom_app
    (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasis F G U fun a => (e a).hom) (a : ι) :
    (moduleSheafIsoOfSectionIsoOnBasis F G U e hU hcomp).hom.val.app (op (U a)) = (e a).hom :=
  moduleSheafHomOfSectionHomOnBasis_app F G U (fun a => (e a).hom) hU hcomp a

/-- The inverse of the assembled isomorphism has `(e a).inv` as its component on `U a`. -/
public theorem moduleSheafIsoOfSectionIsoOnBasis_inv_app
    (hU : Opens.IsBasis (Set.range U))
    (hcomp : IsCompatibleOnBasis F G U fun a => (e a).hom) (a : ι) :
    (moduleSheafIsoOfSectionIsoOnBasis F G U e hU hcomp).inv.val.app (op (U a)) = (e a).inv :=
  moduleSheafHomOfSectionHomOnBasis_app G F U (fun a => (e a).inv) hU
    (isCompatibleOnBasis_inv F G U e hcomp) a

end IsoOfFamily

end Stacks.BasisRestriction

end
