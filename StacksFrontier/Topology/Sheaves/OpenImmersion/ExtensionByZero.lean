module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.Topology.OpenSubspace
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 00A9 — extension by zero along an open immersion is fully faithful

Let `X` be a topological space, `U ⊆ X` an open subset and `j : U → X` the inclusion. Write
`Ab(X)` and `Ab(U)` for the categories of sheaves of abelian groups on `X` and on `U`. Stacks
00A9 says that the extension-by-zero functor `j_! : Ab(U) → Ab(X)` is fully faithful, and that a
sheaf `G` on `X` lies in its essential image exactly when the stalk `G_x` is zero for every
`x ∈ X ∖ U`. Both clauses are proved here, as `jExt_full`/`jExt_faithful` and `jExt_essImage`.

The extension by zero itself is the extension by an initial object of
`StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial`, instantiated at the value
category `AddCommGrpCat`, whose initial object is the zero group: `jExt` is
`TopCat.Presheaf.extendByInitialSheaf` and `restrict` is Mathlib's naive restriction
`TopologicalSpace.Opens.sheafRestrict`. Everything that file provides — the adjunction
`j_! ⊣ j^{-1}` (Stacks 00A5 (2)), the isomorphism `j^{-1} j_! ≅ id` (Stacks 00A5 (5)), the
stalks of `j_! F` (Stacks 00A5 (3)) and full faithfulness — is used here rather than rebuilt,
so what this file adds is exactly the description of the essential image:

* `jExt_stalk_isZero_of_notMem`, the vanishing of the stalks of `j_! F` off `U`, read off the
  general statement `TopCat.Presheaf.isZero_stalk_extendByInitialSheafify`;
* `jExt_counit_isIso_of_vanishing`, the converse input: a sheaf whose stalks vanish off `U` has
  invertible adjunction counit `j_! (j^{-1} G) ⟶ G`. It is checked stalkwise — at a point of `U`
  from the right triangle identity and invertibility of the unit, transported through
  `TopCat.Presheaf.stalkRestrictIso`; at a point outside `U` because both stalks vanish.
-/

@[expose] public section

open TopologicalSpace CategoryTheory Limits Opposite

namespace ExtensionByZero

universe u

variable {X : TopCat.{u}} (U : Opens X)

/-- The open subset `U`, viewed as a topological space (object of `TopCat`) via the
subspace topology. The inclusion `j : U → X` is `U.inclusion'`. This is
`Stacks.Topology.openSubspace` under the name this file uses. -/
abbrev Usp : TopCat.{u} := Stacks.Topology.openSubspace U

/-- The restriction functor `j⁻¹ : Ab(X) → Ab(U)`. For an open immersion the inverse-image
sheaf functor is the naive restriction `G ↦ (W ↦ G(j W))`, which is Mathlib's
`TopologicalSpace.Opens.sheafRestrict`. -/
@[sga "4 IV 11.2.2" "special case"]
noncomputable abbrev restrict :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} (Usp U) :=
  Opens.sheafRestrict U

/-- The extension by zero `j_! : Ab(U) → Ab(X)`: the extension by an initial object at the value
category `AddCommGrpCat`, whose initial object is the zero group. -/
@[sga "2 I 1.6" "Z_{Z, special case",
  sga "4 III 1.9.2",
  sga "4 IV 11.3.1",
  sga "4 XVII 5.1.1",
  sga "4½ Etat_0 6.2" "special case"]
noncomputable abbrev jExt :
    TopCat.Sheaf AddCommGrpCat.{u} (Usp U) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.Presheaf.extendByInitialSheaf U

/-- **`j_! ⊣ j⁻¹`.** Extension by zero is left adjoint to restriction: bifunctorially in
`F` and `G` we have `Mor_{Ab(X)}(j_! F, G) = Mor_{Ab(U)}(F, G|_U)`. -/
@[sga "4 III 1.7" "special case",
  sga "4 III 1.9.2",
  sga "4 IV 11.3.1" "special case",
  sga "4 IV 14.2" "special case",
  sga "4 V 2.2" "special case",
  sga "4 XVII 5.1.1"]
noncomputable abbrev jExtAdjunction : jExt U ⊣ restrict U :=
  TopCat.Presheaf.extendByInitialSheafAdjunction U

/-- The `FullyFaithful` structure on `j_!`, obtained formally from the adjunction `j_! ⊣ j⁻¹`
together with the natural isomorphism `j⁻¹ j_! ≅ id`. -/
@[sga "4 IV 11.3.1" "special case", sga "4 XVII 5.1.1" "j*j! ≅ id"]
noncomputable def jExtFullyFaithful : (jExt U).FullyFaithful :=
  TopCat.Presheaf.extendByInitialSheafFullyFaithful U

/-- **Stacks 00A9 (1).** The extension by zero functor `j_!` is full: every morphism
`j_! F ⟶ j_! F'` of sheaves on `X` comes from a morphism `F ⟶ F'` of sheaves on `U`. -/
@[stacks 00A9 "(1)"]
theorem jExt_full : (jExt U).Full :=
  (jExtFullyFaithful U).full

/-- **Stacks 00A9 (1).** The extension by zero functor `j_!` is faithful: a morphism of sheaves
on `U` is determined by the morphism it induces on the extensions by zero. -/
@[stacks 00A9 "(1)", sga "4 IV 11.3.1" "special case"]
theorem jExt_faithful : (jExt U).Faithful :=
  (jExtFullyFaithful U).faithful

/-- **Stalks of `j_! F` outside `U`.** For any sheaf `F` on `U` and any point `x ∉ U`, the stalk
of `j_! F` at `x` is zero. This is the off-`U` half of the stalk computation of Stacks 00A5 (3),
which is `TopCat.Presheaf.isZero_stalk_extendByInitialSheafify`. -/
@[sga "4 XVII 5.1.1" "partial"]
theorem jExt_stalk_isZero_of_notMem (F : TopCat.Sheaf AddCommGrpCat.{u} (Usp U)) (x : X)
    (hx : x ∉ U) : IsZero (((jExt U).obj F).presheaf.stalk x) :=
  TopCat.Presheaf.isZero_stalk_extendByInitialSheafify U F.presheaf hx

/-- **The counit is an isomorphism when `G` vanishes off `U`.** If the stalk `G_x` is zero for
every `x ∉ U`, then the adjunction counit `j_! (j⁻¹ G) ⟶ G` is an isomorphism. This is the heart
of the "if" direction of Stacks 00A9 (2).

It suffices to check that the counit is an isomorphism on every stalk. At a point of `U` this
follows from the right triangle identity together with invertibility of the unit, transported
through the identification `TopCat.Presheaf.stalkRestrictIso` of the stalks of a restriction. At
a point outside `U` the source stalk vanishes by `jExt_stalk_isZero_of_notMem` and the target
stalk vanishes by hypothesis, and a map between zero objects is an isomorphism. -/
theorem jExt_counit_isIso_of_vanishing (G : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hG : ∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x)) :
    IsIso ((jExtAdjunction U).counit.app G) := by
  have hunit := TopCat.Presheaf.ExtensionByInitial.isIso_unit_extendByInitialSheafAdjunction
    (C := AddCommGrpCat.{u}) U
  -- The right triangle identity turns invertibility of the unit into invertibility of the
  -- restriction of the counit.
  have hR : IsIso ((restrict U).map ((jExtAdjunction U).counit.app G)) :=
    isIso_of_hom_comp_eq_id _ ((jExtAdjunction U).right_triangle_components G)
  have hstalk : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((jExtAdjunction U).counit.app G).hom) := by
    intro x
    by_cases hx : x ∈ U
    · have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
          ((jExtAdjunction U).counit.app G).hom) :=
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (Usp U)).map_isIso
          ((restrict U).map ((jExtAdjunction U).counit.app G))
      simpa using (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
        ((jExtAdjunction U).counit.app G).hom ⟨x, hx⟩).mp inferInstance
    · exact (jExt_stalk_isZero_of_notMem U ((restrict U).obj G) x hx).isIso (hG x hx) _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- **Stacks 00A9 (2), description of the essential image.** An abelian sheaf `G` on `X` lies in
the essential image of `j_!` if and only if the stalk `G_x` is the zero abelian group for every
point `x ∈ X` not belonging to `U`.

For "only if", an isomorphism `G ≅ j_! F` induces an isomorphism of stalks, and the stalk of
`j_! F` at a point outside `U` is zero. For "if", the vanishing hypothesis makes the counit
`j_! (j⁻¹ G) ⟶ G` an isomorphism, which exhibits `G` in the essential image. -/
@[stacks 00A9 "(2)", sga "4 XVII 5.1.1" "partial"]
theorem jExt_essImage (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (jExt U).essImage G ↔ ∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x) := by
  constructor
  · -- only if: stalks of an object in the essential image vanish off `U`
    rintro ⟨F, ⟨e⟩⟩ x hx
    exact (jExt_stalk_isZero_of_notMem U F x hx).of_iso
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((sheafToPresheaf _ _).mapIso e)).symm)
  · -- if: vanishing stalks ⟹ counit iso ⟹ `G` in the essential image
    intro hG
    have := jExt_counit_isIso_of_vanishing U G hG
    exact Functor.essImage.ofIso (asIso ((jExtAdjunction U).counit.app G))
      ((jExt U).obj_mem_essImage _)

end ExtensionByZero
