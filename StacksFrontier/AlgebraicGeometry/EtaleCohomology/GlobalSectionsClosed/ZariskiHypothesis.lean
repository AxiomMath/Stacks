module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed

/-!
# The Zariski hypothesis of Tag 09ZF forces every open containing the closed subscheme to be all

Let `i : Z ⟶ X` be a morphism of schemes and suppose that restriction of global sections along
`i` is bijective for *every* sheaf of sets on the Zariski site of `X`, which is hypothesis (1) of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF). Then the only open subscheme of
`X` containing the image of `i` is `X` itself.

This is the step the source phrases as "every nonempty closed subscheme of `X` meets `Z`": an
open `U` containing the image of `i` has closed complement disjoint from the image, and the
conclusion `U = ⊤` says that complement is empty. Only *surjectivity* of the restriction map is
used, and only for one sheaf per open — the subterminal sheaf of the open.

That sheaf is built here directly. For an open `U` of `X` it has exactly one section over an open
`V ⊆ U` and no sections otherwise, so its global sections are empty unless `U = ⊤`, while the
preimage of `U` in `Z` is all of `Z` as soon as `U` contains the image of `i`, and the unit of the
inverse-image/direct-image adjunction at `U` therefore produces a global section on `Z`.

## Main definitions

* `Stacks.EtaleCohomology.openZariskiPresheaf` — the presheaf of sets on the opens of a scheme
  with one section over the opens contained in a given open and none over the others.
* `Stacks.EtaleCohomology.openZariskiSheaf` — the same, as a sheaf.

## Main results

* `Stacks.EtaleCohomology.isSheaf_openZariskiPresheaf` — the presheaf is a sheaf.
* `Stacks.EtaleCohomology.nonempty_openZariskiPresheaf_iff` — it has a section over an open
  exactly when that open is contained in the given one.
* `Stacks.EtaleCohomology.eq_top_of_zariskiGlobalSectionsMap_surjective` — if restriction of
  global sections along `i` is surjective for every Zariski sheaf of sets, then an open
  containing the image of `i` is everything.

## Implementation notes

The sheaf condition is checked through Mathlib's unique-gluing criterion
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types`, which applies because the site of this
scheme's opens is literally `TopologicalSpace.Opens.grothendieckTopology` of its carrier. The
case distinction one expects — the covered open lies in `U`, or it does not — does not arise:
a compatible family of sections already witnesses that each member of the covering family lies in
`U`, hence so does their supremum, and the type of sections over that supremum is then a
nonempty subsingleton.

Sections are valued in `ULift (PLift _)` rather than in a subtype of `PUnit` so that the
coefficient universe `Type (max (u + 1) v)` of the étale theory is reached without constraining
it, and so that `Subsingleton` is available by instance search.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- The presheaf of sets on the opens of `X` with exactly one section over an open contained in
`U` and no sections over any other open. -/
public def openZariskiPresheaf (U : X.Opens) :
    (Opens X.carrier)ᵒᵖ ⥤ Type (max (u + 1) v) where
  obj V := ULift.{max (u + 1) v, 0} (PLift (V.unop ≤ U))
  map {V W} f := ↾fun (x : ULift.{max (u + 1) v, 0} (PLift (V.unop ≤ U))) ↦
    (ULift.up (PLift.up ((leOfHom f.unop).trans x.down.down)) :
      ULift.{max (u + 1) v, 0} (PLift (W.unop ≤ U)))
  map_id _ := by cat_disch
  map_comp _ _ := by cat_disch

/-- A section of `openZariskiPresheaf U` over `V` witnesses `V ≤ U`. -/
public theorem le_of_openZariskiPresheaf {U : X.Opens} {V : (Opens X.carrier)ᵒᵖ}
    (x : (openZariskiPresheaf.{u, v} U).obj V) : V.unop ≤ U :=
  (show ULift.{max (u + 1) v, 0} (PLift (V.unop ≤ U)) from x).down.down

/-- The section of `openZariskiPresheaf U` over an open contained in `U`. -/
public def openZariskiPresheafMk {U : X.Opens} {V : (Opens X.carrier)ᵒᵖ} (h : V.unop ≤ U) :
    (openZariskiPresheaf.{u, v} U).obj V :=
  (ULift.up (PLift.up h) : ULift.{max (u + 1) v, 0} (PLift (V.unop ≤ U)))

/-- `openZariskiPresheaf U` has at most one section over any open. -/
public theorem openZariskiPresheaf_ext {U : X.Opens} {V : (Opens X.carrier)ᵒᵖ}
    (x y : (openZariskiPresheaf.{u, v} U).obj V) : x = y :=
  Subsingleton.elim (α := ULift.{max (u + 1) v, 0} (PLift (V.unop ≤ U))) x y

/-- The presheaf `openZariskiPresheaf U` has a section over `V` exactly when `V ≤ U`. -/
public theorem nonempty_openZariskiPresheaf_iff (U V : X.Opens) :
    Nonempty ((openZariskiPresheaf.{u, v} U).obj (op V)) ↔ V ≤ U :=
  ⟨fun h ↦ h.elim le_of_openZariskiPresheaf, fun h ↦ ⟨openZariskiPresheafMk h⟩⟩

/-- `openZariskiPresheaf U` is a sheaf. A compatible family of sections over a covering family
already shows that every member of the family is contained in `U`, hence so is the open they
cover, and sections over that open then form a nonempty subsingleton. -/
public theorem isSheaf_openZariskiPresheaf (U : X.Opens) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
      (openZariskiPresheaf.{u, v} U) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr ?_
  intro ι V sf _
  have hle : iSup V ≤ U := iSup_le fun i ↦ le_of_openZariskiPresheaf.{u, v} (sf i)
  exact ⟨openZariskiPresheafMk.{u, v} hle, fun _ ↦ openZariskiPresheaf_ext _ _,
    fun _ _ ↦ openZariskiPresheaf_ext _ _⟩

/-- The subterminal sheaf of sets on the Zariski site of `X` attached to an open subscheme `U`:
one section over the opens contained in `U`, none over the others. -/
public def openZariskiSheaf (U : X.Opens) :
    Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)) :=
  ⟨openZariskiPresheaf.{u, v} U, isSheaf_openZariskiPresheaf.{u, v} U⟩

/-- **The Zariski hypothesis of Tag 09ZF leaves no room outside the closed subscheme.** If
restriction of global sections along `i : Z ⟶ X` is surjective for every sheaf of sets on the
Zariski site of `X`, then an open subscheme of `X` containing the image of `i` is all of `X`.

Applied to the subterminal sheaf of such an open `U`: the preimage of `U` in `Z` is all of `Z`,
so the unit of the adjunction at `U` sends the unique section over `U` to a global section on
`Z`; surjectivity produces a global section on `X`, which exists only if `U = ⊤`. -/
public theorem eq_top_of_zariskiGlobalSectionsMap_surjective {Z : Scheme.{u}} (i : Z ⟶ X)
    (hZar : ∀ F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v)),
      Function.Surjective (zariskiGlobalSectionsMap.{u, v} i F))
    {U : X.Opens} (hU : Set.range i.base ⊆ (U : Set X)) : U = ⊤ := by
  have hpre : (Opens.map i.base).obj U = ⊤ := by
    ext z
    simpa using hU ⟨z, rfl⟩
  have hsec := (((Opens.map i.base).sheafAdjunctionContinuous
    (Type (max (u + 1) v)) (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Z.carrier)).unit.app
      (openZariskiSheaf.{u, v} U)).hom.app (op U)
      (openZariskiPresheafMk.{u, v} (V := op U) (le_refl U))
  obtain ⟨s, -⟩ := hZar (openZariskiSheaf.{u, v} U) (hpre ▸ hsec)
  exact top_le_iff.mp (le_of_openZariskiPresheaf.{u, v} (V := op ⊤) s)

end Stacks.EtaleCohomology

end
