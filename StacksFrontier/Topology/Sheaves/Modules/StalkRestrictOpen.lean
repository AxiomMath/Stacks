module

public import Mathlib.Geometry.RingedSpace.Stalks
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Restricting to an open does not change the stalk of a sheaf of modules

Let `f : Z ⟶ Y` be an open embedding of topological spaces, let `O` be a sheaf of rings on `Y`
and let `z : Z`. Restricting along `f` sends a sheaf of `O`-modules `M` to a sheaf of modules
over the restricted sheaf of rings `O|_Z` (`Stacks.SheafOfModules.restrictSheafOfModules`), and
on underlying presheaves this is precomposition with `V ↦ f '' V`. Since the opens of the form
`f '' V` with `z ∈ V` are cofinal among the open neighbourhoods of `f z`, the stalk of `M|_Z`
at `z` is the stalk of `M` at `f z`.

This file proves that, as an isomorphism which is *natural in the module* and *semilinear* over
the corresponding isomorphism `(O|_Z)_z ≅ O_{f z}` of stalk rings. Both underlying
identifications are Mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso`, read on the
presheafed space `(Y, O)` for the rings and on the presheafed space `(Y, M)` of underlying
abelian groups for the modules; the content added here is that the second is semilinear over the
first, and that it is natural in `M`.

## Main definitions

* `Stacks.SheafOfModules.restrictStalkRingIso`: the isomorphism `(O|_Z)_z ≅ O_{f z}` of stalk
  rings.
* `Stacks.SheafOfModules.restrictStalkAddIso`: the isomorphism `(M|_Z)_z ≅ M_{f z}` of stalks of
  abelian groups.
* `Stacks.SheafOfModules.stalkRestrictHom` and `Stacks.SheafOfModules.stalkRestrictIso`: the
  previous isomorphism read as a map of `(O|_Z)_z`-modules, the target carrying the action
  obtained by restricting scalars along `restrictStalkRingIso`.
* `Stacks.SheafOfModules.stalkRestrictNatIso`: **the comparison, as an isomorphism of
  functors** `restrictSheafOfModules hf O ⋙ stalkFunctor (O|_Z) z ≅ stalkFunctor O (f z) ⋙
  ModuleCat.restrictScalars restrictStalkRingIso`.
* `AlgebraicGeometry.RingedSpace.restrictModulesStalkRingIso` and
  `AlgebraicGeometry.RingedSpace.restrictModulesStalkNatIso`: the same for the restriction of
  `O_W`-modules to an open `U` of a bare ringed space `W`, at a point `y ∈ U`.

## Main results

* `Stacks.SheafOfModules.restrictStalkAddIso_hom_smul`: **semilinearity.** The identification of
  stalks of modules carries `r • m` to `(restrictStalkRingIso r) • (identification of m)`.
* `Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap`: the identification is natural in
  the sheaf of modules.

## Implementation notes

**Why this is not the scheme-level statement.** For modules on a *scheme* there is a
restriction functor along an open immersion and a stalk comparison for it. The ringed spaces
this file is about need not be schemes — the motivating case is `(X, f⁻¹O_Y)` for a continuous
map `f` — so none of that applies, and the comparison has to be built from the bare
presheafed-space statement.

**Everything is definitional except the scalars.** `restrictSheafOfRings` and
`restrictSheafOfModules` are precomposition with `V ↦ f '' V` on underlying presheaves, which is
exactly how `AlgebraicGeometry.PresheafedSpace.restrict` defines the restricted structure
presheaf. So `((Y, O).restrict hf).presheaf` *is* `(O|_Z).obj` and `((Y, M).restrict hf).presheaf`
*is* `(M|_Z).val.presheaf`, and Mathlib's `restrictStalkIso` can be used verbatim in `RingCat`
and in `AddCommGrpCat`. The one genuine statement is the semilinearity, and it is checked on
germs: there both stalk identifications are
`AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ`, which turns the germ of a
section over `V ⊆ Z` into the germ of the same section over `f '' V`, and the identity to prove
becomes `PresheafOfModules.germ_ringCat_smul` for `M` over the open `f '' V` of `Y`. The
reduction of a pair `(r, m)` of stalk elements to germs over a common open uses
`TopCat.Presheaf.exists_le_germ_eq`, which produces the open for the scalar inside the open for
the section, so one restriction suffices.

**Naturality** is proved, not assumed: every element of a stalk is the germ of a section
(`TopCat.Presheaf.exists_germ_eq`), and on the germ over `V` both sides of the square are the
germ at `f z` of the component of `g` over `f '' V`.

**Universes.** A single universe `u` carries the spaces, the rings and the module sections
together, as everywhere in the stalk API for sheaves of modules on a space
(`AlgebraicGeometry.SheafOfModules.stalkFunctor` is stated that way, because the filtered
colimit computing the stalk is indexed by the opens of the space).

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

/-! ### The stalk of a morphism of sheaves of modules, on germs -/

section Germ

variable {X : TopCat.{u}} {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (x : X)

/-- The stalk at `x` of a morphism of sheaves of modules sends the germ of a section to the germ
of its image. -/
theorem stalkFunctor_map_germ_apply {M N : _root_.SheafOfModules.{u} R} (g : M ⟶ N)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor R x).map g
        (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      TopCat.Presheaf.germ N.val.presheaf U x hx (g.val.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf R.obj).map g.val) m

end Germ

/-! ### The two stalk identifications -/

variable {Y Z : TopCat.{u}} {f : Z ⟶ Y} (hf : IsOpenEmbedding f)
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (z : Z)

/-- **The stalk of the restriction of a sheaf of rings to an open is the stalk of the sheaf.**
This is Mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso` for the presheafed space
`(Y, O)` in `RingCat`: the restricted structure presheaf of that presheafed space is
definitionally `Stacks.SheafOfModules.restrictSheafOfRings hf O`. -/
def restrictStalkRingIso :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (restrictSheafOfRings hf O).obj z ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj (f z) :=
  PresheafedSpace.restrictStalkIso (⟨Y, O.obj⟩ : PresheafedSpace RingCat.{u}) hf z

/-- On germs, `restrictStalkRingIso` sends the germ at `z` of a section of `O` over `f '' V` to
its germ at `f z`. -/
@[reassoc]
theorem restrictStalkRingIso_hom_germ (V : Opens Z) (hz : z ∈ V) :
    TopCat.Presheaf.germ (restrictSheafOfRings hf O).obj V z hz ≫
        (restrictStalkRingIso hf O z).hom =
      TopCat.Presheaf.germ O.obj (hf.functor.obj V) (f z) ⟨z, hz, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ
    (⟨Y, O.obj⟩ : PresheafedSpace RingCat.{u}) hf V z hz

/-- `Stacks.SheafOfModules.restrictStalkRingIso_hom_germ` on elements. -/
theorem restrictStalkRingIso_hom_germ_apply (V : Opens Z) (hz : z ∈ V)
    (r : (restrictSheafOfRings hf O).obj.obj (op V)) :
    (restrictStalkRingIso hf O z).hom
        (TopCat.Presheaf.germ (restrictSheafOfRings hf O).obj V z hz r) =
      TopCat.Presheaf.germ O.obj (hf.functor.obj V) (f z) ⟨z, hz, rfl⟩ r :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (⟨Y, O.obj⟩ : PresheafedSpace RingCat.{u}) hf V z hz r

variable (M : _root_.SheafOfModules.{u} O)

/-- **The stalk of the restriction of a sheaf of modules to an open is the stalk of the sheaf**,
as an isomorphism of abelian groups. This is Mathlib's
`AlgebraicGeometry.PresheafedSpace.restrictStalkIso` for the presheafed space `(Y, M)` in
`AddCommGrpCat`: the underlying presheaf of abelian groups of the restriction of `M` is
definitionally the restricted structure presheaf of that presheafed space. -/
def restrictStalkAddIso :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf z ≅
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (f z) :=
  PresheafedSpace.restrictStalkIso (⟨Y, M.val.presheaf⟩ : PresheafedSpace AddCommGrpCat.{u}) hf z

/-- On germs, `restrictStalkAddIso` sends the germ at `z` of a section of `M` over `f '' V` to
its germ at `f z`. -/
@[reassoc]
theorem restrictStalkAddIso_hom_germ (V : Opens Z) (hz : z ∈ V) :
    TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz ≫
        (restrictStalkAddIso hf O z M).hom =
      TopCat.Presheaf.germ M.val.presheaf (hf.functor.obj V) (f z) ⟨z, hz, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ
    (⟨Y, M.val.presheaf⟩ : PresheafedSpace AddCommGrpCat.{u}) hf V z hz

/-- `Stacks.SheafOfModules.restrictStalkAddIso_hom_germ` on elements. -/
theorem restrictStalkAddIso_hom_germ_apply (V : Opens Z) (hz : z ∈ V)
    (m : ((restrictSheafOfModules.{u} hf O).obj M).val.obj (op V)) :
    (restrictStalkAddIso hf O z M).hom
        (TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz m) =
      TopCat.Presheaf.germ M.val.presheaf (hf.functor.obj V) (f z) ⟨z, hz, rfl⟩ m :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (⟨Y, M.val.presheaf⟩ : PresheafedSpace AddCommGrpCat.{u}) hf V z hz m

/-! ### Semilinearity -/

/-- Semilinearity on germs: both identifications turn a germ over `V` into the germ of the same
section over `f '' V`, so the statement becomes the germ-semilinearity of the action of `O` on
`M` over the open `f '' V` of `Y`. -/
theorem restrictStalkAddIso_hom_germ_smul (V : Opens Z) (hz : z ∈ V)
    (r : (restrictSheafOfRings hf O).obj.obj (op V))
    (m : ((restrictSheafOfModules.{u} hf O).obj M).val.obj (op V)) :
    (restrictStalkAddIso hf O z M).hom
        (TopCat.Presheaf.germ (restrictSheafOfRings hf O).obj V z hz r •
          TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz m) =
      (restrictStalkRingIso hf O z).hom
          (TopCat.Presheaf.germ (restrictSheafOfRings hf O).obj V z hz r) •
        (restrictStalkAddIso hf O z M).hom
          (TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz
            m) := by
  rw [← PresheafOfModules.germ_ringCat_smul ((restrictSheafOfModules.{u} hf O).obj M).val z V hz
      r m, restrictStalkAddIso_hom_germ_apply, restrictStalkAddIso_hom_germ_apply,
    restrictStalkRingIso_hom_germ_apply]
  exact PresheafOfModules.germ_ringCat_smul M.val (f z) (hf.functor.obj V) ⟨z, hz, rfl⟩ r m

/-- **The identification of stalks of modules is semilinear** over the identification of stalks
of rings.

Both stalk elements are germs of sections, and `TopCat.Presheaf.exists_le_germ_eq` produces the
open for the scalar inside the open for the section, so a single restriction puts both over one
open `V ∋ z`; there the statement is `Stacks.SheafOfModules.restrictStalkAddIso_hom_germ_smul`. -/
theorem restrictStalkAddIso_hom_smul
    (r : TopCat.Presheaf.stalk (C := RingCat.{u}) (restrictSheafOfRings hf O).obj z)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf z) :
    (restrictStalkAddIso hf O z M).hom (r • m) =
      (restrictStalkRingIso hf O z).hom r • (restrictStalkAddIso hf O z M).hom m := by
  obtain ⟨V₂, hV₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq
    ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf m
  obtain ⟨V, hle, hV, r₀, hr⟩ := TopCat.Presheaf.exists_le_germ_eq
    (restrictSheafOfRings hf O).obj r hV₂
  have hm' : TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hV
      (((restrictSheafOfModules.{u} hf O).obj M).val.map (homOfLE hle).op m₀) = m :=
    (TopCat.Presheaf.germ_res_apply
      ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf (homOfLE hle) z hV m₀).trans hm
  rw [← hr, ← hm']
  exact restrictStalkAddIso_hom_germ_smul hf O z M V hV r₀ _

/-! ### Naturality -/

/-- Naturality on germs: the germ over `V ⊆ Z` of a section of `M|_Z` is carried by both routes
to the germ at `f z` of the component of `g` over `f '' V`. -/
theorem restrictStalkAddIso_hom_stalkMap_germ {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (V : Opens Z) (hz : z ∈ V)
    (m : ((restrictSheafOfModules.{u} hf O).obj M).val.obj (op V)) :
    (restrictStalkAddIso hf O z N).hom
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (restrictSheafOfRings hf O) z).map
          ((restrictSheafOfModules.{u} hf O).map g)
          (TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz
            m)) =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O (f z)).map g
        ((restrictStalkAddIso hf O z M).hom
          (TopCat.Presheaf.germ ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf V z hz
            m)) := by
  have h₁ := stalkFunctor_map_germ_apply z ((restrictSheafOfModules.{u} hf O).map g) V hz m
  have h₂ := restrictStalkAddIso_hom_germ_apply hf O z N V hz
    (((restrictSheafOfModules.{u} hf O).map g).val.app (op V) m)
  have h₃ := restrictStalkAddIso_hom_germ_apply hf O z M V hz m
  have h₄ := stalkFunctor_map_germ_apply (f z) g (hf.functor.obj V) ⟨z, hz, rfl⟩ m
  rw [h₁, h₂, h₃, h₄]
  rfl

/-- **The identification of stalks of modules is natural in the sheaf of modules.**

Every element of the stalk is the germ of a section over some `V ∋ z`, where the statement is
`Stacks.SheafOfModules.restrictStalkAddIso_hom_stalkMap_germ`. -/
theorem restrictStalkAddIso_hom_stalkMap {M N : _root_.SheafOfModules.{u} O} (g : M ⟶ N)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf z) :
    (restrictStalkAddIso hf O z N).hom
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (restrictSheafOfRings hf O) z).map
          ((restrictSheafOfModules.{u} hf O).map g) m) =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O (f z)).map g
        ((restrictStalkAddIso hf O z M).hom m) := by
  obtain ⟨V, hzV, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((restrictSheafOfModules.{u} hf O).obj M).val.presheaf m
  exact restrictStalkAddIso_hom_stalkMap_germ hf O z g V hzV m₀

/-! ### The comparison isomorphism of modules -/

/-- **The comparison map of `(O|_Z)_z`-modules**: the stalk at `z` of the restriction of `M` to
`Z` maps to the stalk of `M` at `f z` with its scalars restricted along
`restrictStalkRingIso`. On underlying abelian groups it is `restrictStalkAddIso`. -/
def stalkRestrictHom :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (restrictSheafOfRings hf O) z).obj
        ((restrictSheafOfModules.{u} hf O).obj M) ⟶
      (ModuleCat.restrictScalars.{u} (restrictStalkRingIso hf O z).hom.hom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O (f z)).obj M) :=
  ConcreteCategory.ofHom
    (C := ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (restrictSheafOfRings hf O).obj z))
    { toFun := fun m => (restrictStalkAddIso hf O z M).hom m
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => restrictStalkAddIso_hom_smul hf O z M r m }

/-- On underlying abelian groups the comparison map is `restrictStalkAddIso`. -/
theorem forget₂_map_stalkRestrictHom :
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (restrictSheafOfRings hf O).obj z)) AddCommGrpCat.{u}).map
        (stalkRestrictHom hf O z M) =
      (restrictStalkAddIso hf O z M).hom := by
  ext m
  rfl

/-- The comparison map `stalkRestrictHom` is an isomorphism of `(O|_Z)_z`-modules. -/
instance isIso_stalkRestrictHom : IsIso (stalkRestrictHom hf O z M) := by
  rw [← isIso_iff_of_reflects_iso _
      (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
        (restrictSheafOfRings hf O).obj z)) AddCommGrpCat.{u}),
    forget₂_map_stalkRestrictHom]
  exact Iso.isIso_hom _

/-- **The stalk at `z` of the restriction of `M` to an open is the stalk of `M` at `f z`**, as an
isomorphism of `(O|_Z)_z`-modules, the target carrying the action obtained by restricting
scalars along `restrictStalkRingIso`. -/
def stalkRestrictIso :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (restrictSheafOfRings hf O) z).obj
        ((restrictSheafOfModules.{u} hf O).obj M) ≅
      (ModuleCat.restrictScalars.{u} (restrictStalkRingIso hf O z).hom.hom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor O (f z)).obj M) :=
  asIso (stalkRestrictHom hf O z M)

/-- **The stalk comparison across restriction to an open, as an isomorphism of functors.**

Restricting a sheaf of `O`-modules to the open `Z` and taking its stalk at `z` is taking its
stalk at `f z` and restricting scalars along the isomorphism `(O|_Z)_z ≅ O_{f z}` of stalk
rings. -/
def stalkRestrictNatIso :
    restrictSheafOfModules.{u} hf O ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor (restrictSheafOfRings hf O) z ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor O (f z) ⋙
        ModuleCat.restrictScalars.{u} (restrictStalkRingIso hf O z).hom.hom :=
  NatIso.ofComponents (stalkRestrictIso hf O z) fun {M N} g => by
    ext m
    exact restrictStalkAddIso_hom_stalkMap hf O z g m

end Stacks.SheafOfModules

/-! ### The ringed-space idiom -/

namespace AlgebraicGeometry.RingedSpace

open Stacks.SheafOfModules StrictlyPerfect

variable (W : AlgebraicGeometry.RingedSpace.{u, u}) (U : Opens W.carrier)
  {y : W.carrier} (hy : y ∈ U)

/-- **The stalk of the structure sheaf of an open subspace of a ringed space is the stalk of the
structure sheaf**: `O_{W|U, y} ≅ O_{W, y}` for `y ∈ U`, an isomorphism in `RingCat`, the
structure sheaf being read as a sheaf of (not necessarily commutative) rings. -/
def restrictModulesStalkRingIso :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafOfRings (W.restrict U.isOpenEmbedding)).obj ⟨y, hy⟩ ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafOfRings W).obj y :=
  restrictStalkRingIso U.isOpenEmbedding (structureSheafOfRings W) ⟨y, hy⟩

/-- **The stalk comparison across restriction of `O_W`-modules to an open `U` of a bare ringed
space `W`, as an isomorphism of functors.**

For `y ∈ U`, restricting an `O_W`-module to `U` and taking its stalk at `y` is taking its stalk
at `y` on `W` and restricting scalars along `restrictModulesStalkRingIso`. The ringed space `W`
is *not* assumed to be a scheme, which is what rules out the scheme-level restriction functors
and their stalk comparisons. -/
def restrictModulesStalkNatIso :
    restrictModules.{u, u, u} W U ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings (W.restrict U.isOpenEmbedding)) ⟨y, hy⟩ ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings W) y ⋙
        ModuleCat.restrictScalars.{u} (restrictModulesStalkRingIso W U hy).hom.hom :=
  stalkRestrictNatIso U.isOpenEmbedding (structureSheafOfRings W) ⟨y, hy⟩

end AlgebraicGeometry.RingedSpace

end
