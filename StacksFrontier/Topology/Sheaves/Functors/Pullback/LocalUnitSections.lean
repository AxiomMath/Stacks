module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageRestrictScalars

/-!
# Sections of an inverse image are locally induced sections

Let `f : X ⟶ Y` be a continuous map and `F` a sheaf on `Y`. The sections of the inverse image
`f⁻¹F` have no description, but each of them is, near every point, the restriction of the section
`η(t)` of `f⁻¹F` over `f⁻¹V` induced by a section `t` of `F` over an open `V` of `Y` (the unit of
the adjunction `f⁻¹ ⊣ f_*`), and two induced sections agree near a point `x` only if the
sections they come from agree near `f x`. This file records these two facts, for sheaves with
values in a concrete category and for the inverse image of sheaves of modules, together with the
two ways of using them on a sheaf: two sections which agree locally are equal, and a section
which is locally in the image of a sectionwise injective morphism of sheaves of modules is in
its image.

## Main results

* `Stacks.Topology.exists_restrict_eq_unit`, `Stacks.Topology.exists_restrict_eq_of_unit_eq`:
  the two facts for the inverse image of a sheaf with values in a concrete category.
* `Stacks.Topology.exists_restrict_eq_moduleUnit`,
  `Stacks.Topology.exists_restrict_eq_of_moduleUnit_eq`: the two facts for the inverse image of
  a sheaf of modules over a sheaf of commutative rings.
* `Stacks.Topology.sheaf_eq_of_locally_eq`, `Stacks.Topology.sheafOfModules_eq_of_locally_eq`:
  sections of a sheaf, resp. a sheaf of modules, which agree near every point are equal.
* `Stacks.Topology.exists_app_eq_of_locally`: a section which is near every point in the image of
  a sectionwise injective morphism of sheaves of modules is in its image.

## Implementation notes

Both facts are germ computations: the stalk comparison `F_{f x} ≅ (f⁻¹F)_x` carries the germ of
`t` to the germ of `η(t)` (`Stacks.Topology.germ_unit_app`, resp.
`AlgebraicGeometry.SheafOfModules.inverseImageStalkHom_germ`), it is surjective, and it is
injective. Restrictions are always written with `homOfLE`, so that two restrictions between the
same opens are equal by `Subsingleton.elim` of the morphisms of opens.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology

universe v u w

section Concrete

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- **A section of an inverse image is near every point the restriction of an induced
section.** -/
theorem exists_restrict_eq_unit (F : Y.Sheaf C) {U : Opens X}
    (s : ToType (((TopCat.Sheaf.pullback C f).obj F).presheaf.obj (op U))) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens Y) (_ : f x ∈ V) (t : ToType (F.presheaf.obj (op V))) (W : Opens X)
      (_ : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ (Opens.map f).obj V),
      ((TopCat.Sheaf.pullback C f).obj F).presheaf.map (homOfLE hWU).op s =
        ((TopCat.Sheaf.pullback C f).obj F).presheaf.map (homOfLE hWV).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op V) t) := by
  obtain ⟨V, hV, t, ht⟩ := exists_ambientSection_germ f F x
    (((TopCat.Sheaf.pullback C f).obj F).presheaf.germ U x hx s)
  have h := (germ_unit_app f F V x hV t).trans ht
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq _ x hx hV s _ h.symm
  exact ⟨V, hV, t, W, hxW, iU.le, iV.le, e⟩

/-- **Two induced sections agree near a point only if the sections they come from agree near its
image.** -/
theorem exists_restrict_eq_of_unit_eq (F : Y.Sheaf C) {V : Opens Y}
    (t t' : ToType (F.presheaf.obj (op V))) {W : Opens X} (x : X) (hx : x ∈ W)
    (hWV : W ≤ (Opens.map f).obj V)
    (h : ((TopCat.Sheaf.pullback C f).obj F).presheaf.map (homOfLE hWV).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op V) t) =
        ((TopCat.Sheaf.pullback C f).obj F).presheaf.map (homOfLE hWV).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (op V) t')) :
    ∃ (V' : Opens Y) (_ : f x ∈ V') (hV' : V' ≤ V),
      F.presheaf.map (homOfLE hV').op t = F.presheaf.map (homOfLE hV').op t' := by
  have hxV : f x ∈ V := hWV hx
  have hg := TopCat.Presheaf.germ_ext ((TopCat.Sheaf.pullback C f).obj F).presheaf
    (hxU := hWV hx) (hxV := hWV hx) W hx (homOfLE hWV) (homOfLE hWV) h
  have hg' := ((germ_unit_app f F V x hxV t).symm.trans hg).trans (germ_unit_app f F V x hxV t')
  obtain ⟨V', hV', i, i', e⟩ :=
    TopCat.Presheaf.germ_eq _ (f x) hxV hxV t t' (ambientStalkHom_injective f F x hg')
  refine ⟨V', hV', i.le, ?_⟩
  rw [show homOfLE i.le = i from Subsingleton.elim _ _, e,
    show i' = i from Subsingleton.elim _ _]

omit [HasColimits C] [PreservesFilteredColimits (forget C)] in
/-- **Sections of a sheaf which agree near every point are equal.** -/
theorem sheaf_eq_of_locally_eq {Z : TopCat.{v}} (F : Z.Sheaf C) {U : Opens Z}
    (s t : ToType (F.presheaf.obj (op U)))
    (h : ∀ x ∈ U, ∃ (W : Opens Z) (_ : x ∈ W) (hWU : W ≤ U),
      F.presheaf.map (homOfLE hWU).op s = F.presheaf.map (homOfLE hWU).op t) : s = t := by
  choose W hxW hWU e using h
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : U => W x.1 x.2) U
    (fun x => homOfLE (hWU x.1 x.2)) ?_ s t (fun x => e x.1 x.2)
  intro x hx
  exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW x hx⟩

end Concrete

section Modules

open AlgebraicGeometry.SheafOfModules

variable {Z : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}}

/-- The sheaf of abelian groups underlying a sheaf of modules on a space. -/
noncomputable abbrev sheafOfModulesAb (M : _root_.SheafOfModules.{u} R) :
    TopCat.Sheaf AddCommGrpCat.{u} Z :=
  ⟨M.val.presheaf, M.isSheaf⟩

/-- **Sections of a sheaf of modules which agree near every point are equal.** -/
theorem sheafOfModules_eq_of_locally_eq (M : _root_.SheafOfModules.{u} R) {U : Opens Z}
    (s t : M.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (W : Opens Z) (_ : x ∈ W) (hWU : W ≤ U),
      M.val.map (homOfLE hWU).op s = M.val.map (homOfLE hWU).op t) : s = t :=
  sheaf_eq_of_locally_eq (sheafOfModulesAb M) (U := U) s t h

/-- **A section which is near every point in the image of a sectionwise injective morphism of
sheaves of modules is in its image.** The local preimages agree on overlaps by injectivity, so
they glue, and the gluing is a preimage because the target is a sheaf. -/
theorem exists_app_eq_of_locally {M N : _root_.SheafOfModules.{u} R} (φ : M ⟶ N)
    (hinj : ∀ (V : Opens Z), Function.Injective (φ.val.app (op V))) {U : Opens Z}
    (a : N.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (W : Opens Z) (_ : x ∈ W) (hWU : W ≤ U) (m : M.val.obj (op W)),
      φ.val.app (op W) m = N.val.map (homOfLE hWU).op a) :
    ∃ m : M.val.obj (op U), φ.val.app (op U) m = a := by
  choose W hxW hWU m hm using h
  let ι := U
  let W' : ι → Opens Z := fun x => W x.1 x.2
  have hcomp : TopCat.Presheaf.IsCompatible (sheafOfModulesAb M).presheaf W'
      (fun x => m x.1 x.2) := by
    intro x y
    apply hinj
    change φ.val.app (op (W' x ⊓ W' y)) (M.val.map (Opens.infLELeft (W' x) (W' y)).op (m x.1 x.2)) =
      φ.val.app (op (W' x ⊓ W' y)) (M.val.map (Opens.infLERight (W' x) (W' y)).op (m y.1 y.2))
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hm, hm,
      ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (sheafOfModulesAb M) W' U
    (fun x => homOfLE (hWU x.1 x.2))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW x hx⟩) (fun x => m x.1 x.2) hcomp
  let s' : M.val.obj (op U) := s
  have hs' : ∀ i : ι, M.val.map (homOfLE (hWU i.1 i.2)).op s' = m i.1 i.2 := hs
  refine ⟨s', sheafOfModules_eq_of_locally_eq N _ a fun x hx => ⟨W x hx, hxW x hx, hWU x hx, ?_⟩⟩
  rw [← PresheafOfModules.naturality_apply, hs' ⟨x, hx⟩, hm]

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X)
  (M : _root_.SheafOfModules.{u} (underlyingRingSheaf O))

/-- **A section of an inverse image of a sheaf of modules is near every point the restriction of
an induced section.** -/
theorem exists_restrict_eq_moduleUnit {U : Opens Y} (s : (inverseImageModule f O M).val.obj (op U))
    (y : Y) (hy : y ∈ U) :
    ∃ (V : Opens X) (_ : f y ∈ V) (m : M.val.obj (op V)) (W : Opens Y) (_ : y ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map f).obj V),
      (inverseImageModule f O M).val.map (homOfLE hWU).op s =
        (inverseImageModule f O M).val.map (homOfLE hWV).op
          ((inverseImageModuleUnit f O M).val.app (op V) m) := by
  obtain ⟨t, ht⟩ := (inverseImageStalkHom_bijective f O M y).2
    (TopCat.Presheaf.germ (inverseImageModule f O M).val.presheaf U y hy s)
  obtain ⟨V, hV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  have ht' := (inverseImageStalkHom_germ f O M y V hV m).symm.trans ht
  obtain ⟨W, hyW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (inverseImageModule f O M).val.presheaf
    y hy hV s ((inverseImageModuleUnit f O M).val.app (op V) m) ht'.symm
  exact ⟨V, hV, m, W, hyW, iU.le, iV.le, e⟩

/-- **Two induced sections of an inverse image of a sheaf of modules agree near a point only if
the sections they come from agree near its image.** -/
theorem exists_restrict_eq_of_moduleUnit_eq {V : Opens X} (m m' : M.val.obj (op V))
    {W : Opens Y} (y : Y) (hy : y ∈ W) (hWV : W ≤ (Opens.map f).obj V)
    (h : (inverseImageModule f O M).val.map (homOfLE hWV).op
          ((inverseImageModuleUnit f O M).val.app (op V) m) =
        (inverseImageModule f O M).val.map (homOfLE hWV).op
          ((inverseImageModuleUnit f O M).val.app (op V) m')) :
    ∃ (V' : Opens X) (_ : f y ∈ V') (hV' : V' ≤ V),
      M.val.map (homOfLE hV').op m = M.val.map (homOfLE hV').op m' := by
  have hyV : f y ∈ V := hWV hy
  have hg := TopCat.Presheaf.germ_ext (inverseImageModule f O M).val.presheaf
    (hxU := hWV hy) (hxV := hWV hy) W hy (homOfLE hWV) (homOfLE hWV) h
  have hg' := ((inverseImageStalkHom_germ f O M y V hyV m).trans hg).trans
    (inverseImageStalkHom_germ f O M y V hyV m').symm
  obtain ⟨V', hV', i, i', e⟩ := TopCat.Presheaf.germ_eq M.val.presheaf (f y) hyV hyV m m'
    ((inverseImageStalkHom_bijective f O M y).1 hg')
  refine ⟨V', hV', i.le, ?_⟩
  change M.val.presheaf.map _ m = M.val.presheaf.map _ m'
  rw [show homOfLE i.le = i from Subsingleton.elim _ _, e,
    show i' = i from Subsingleton.elim _ _]

end Modules

end Stacks.Topology

end
