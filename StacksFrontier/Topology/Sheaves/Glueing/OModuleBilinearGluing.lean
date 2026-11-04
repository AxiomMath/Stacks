module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Glueing bilinear maps and global sections of sheaves of `𝒪`-modules over an open covering

`StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluing.lean` glues *morphisms* of presheaves of
`𝒪`-modules over an open covering. The two other kinds of datum that an algebra structure on a
sheaf of modules consists of — a **multiplication**, i.e. an `𝒪`-bilinear map, and a **unit**,
i.e. a global section — are not morphisms, and nothing glued them.

This file glues both, over an arbitrary open covering of an arbitrary topological space, for an
arbitrary presheaf of rings `𝒪`, with only the *target* assumed to be a sheaf. The proofs are the
one-variable ones of `TopCat.Sheaf.LocalModuleHom` carried out in two variables and in none; the
sheaf axiom is used through `TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf` and
`TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf` exactly as there.

## Main definitions

* `TopCat.Sheaf.LocalBilinearMap`: an `𝒪`-bilinear map of presheaves of `𝒪`-modules on an open
  `U` of `X`, recorded as presheaf-level data on the opens of `X` contained in `U` — the
  two-variable analogue of `TopCat.Sheaf.LocalModuleHom`.
* `TopCat.Sheaf.LocalBilinearMap.gluedBilinearMap`: **the glued bilinear map**, as a
  `Stacks.BilinearMap` on the whole space.
* `TopCat.Sheaf.LocalSectionData`: a global section of a presheaf of `𝒪`-modules over an open
  `U`, recorded in the same style: a section over every open contained in `U`, compatible with
  restriction.
* `TopCat.Sheaf.LocalSectionData.gluedSections`: **the glued global section**, as an element of
  `PresheafOfModules.sections`.

## Main results

* `TopCat.Sheaf.existsUnique_bilinearMap_of_localBilinearMap`: **bilinear maps of sheaves of
  `𝒪`-modules glue over an open covering.** A family of local bilinear maps agreeing on all
  overlaps comes from exactly one bilinear map.
* `TopCat.Sheaf.existsUnique_sections_of_localSectionData`: **global sections of a sheaf of
  `𝒪`-modules glue over an open covering.**
* `TopCat.Sheaf.eq_bilinearMap_of_restrict` and `TopCat.Sheaf.eq_sections_of_restrict`: the
  uniqueness halves on their own, with no compatibility hypothesis on the local data.

## Implementation notes

The local data is indexed by the opens of `X` contained in `U`, not by the opens of the subspace
`U`, for the reason recorded in `OModuleMapGluing.lean`: an overlap of two members of the covering
is then a single open of `X`, and the compatibility hypothesis can be — and is — stated over
*every* open contained in two members, so the overlaps are never required to belong to the
covering family.

Bilinearity of the local data is recorded as a family of `AddMonoidHom`-valued `AddMonoidHom`s
together with the two scalar laws, which is the shape `Stacks.BilinearMap` has; no tensor product
of presheaves of modules and no sheafification occurs anywhere, and the glued object is produced
field-for-field.

Only the sheaf condition for the *target* is used. For the bilinear map that is the third module
`P`; for the global section it is the module the section lives in, which is the only module in
sight. The two source modules of a bilinear map are arbitrary presheaves of `𝒪`-modules.

Restriction is used in the bundled semilinear form `PresheafOfModules.resLE` throughout, and
containment proofs are never transported, for the two reasons `OModuleMapGluing.lean` records:
the codomain of `resLE` is literally the module of sections, and proof irrelevance is
definitional.

## No tag is claimed

This is infrastructure. The glueing of a multiplication and a unit is the second half of what
Tag 01NR's `algebra` field needs — the first being the glued homogeneous pieces, which
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` supplies — but no assertion of any
tag is made here: no covering, no scheme and no graded algebra appears.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- Restricting to `W` and then to `W ⊓ U` is restricting to `V ⊓ U` and then to `W ⊓ U`. -/
private theorem resLE_inf_le_left_resLE {M : PresheafOfModules.{u} 𝒪} {U V W : Opens X}
    (hWV : W ≤ V) (x : M.obj (op V)) :
    M.resLE (inf_le_left : W ⊓ U ≤ W) (M.resLE hWV x)
      = M.resLE (inf_le_inf_right U hWV) (M.resLE (inf_le_left : V ⊓ U ≤ V) x) := by
  rw [M.resLE_resLE, M.resLE_resLE]

/-! ### Local bilinear maps of presheaves of `𝒪`-modules -/

/-- An *`𝒪`-bilinear map of presheaves of `𝒪`-modules* `M × N → P` on an open subset `U` of `X`:
a biadditive map on sections over each open `V` of `X` contained in `U`, linear over `𝒪(V)` in
each variable and compatible with all restriction maps.

This is the two-variable analogue of `TopCat.Sheaf.LocalModuleHom`, and the same data as a
`Stacks.BilinearMap` of the restrictions of `M`, `N` and `P` to `U`, recorded on the opens of `X`
inside `U` so that no transport along an order isomorphism of lattices of opens is needed. -/
structure LocalBilinearMap (M N P : PresheafOfModules.{u} 𝒪) (U : Opens X) where
  /-- The biadditive map on sections over an open `V ≤ U`. -/
  app : ∀ (V : Opens X), V ≤ U → M.obj (op V) →+ N.obj (op V) →+ P.obj (op V)
  /-- Linearity over `𝒪(V)` in the first variable. -/
  map_smul_left : ∀ (V : Opens X) (hV : V ≤ U) (r : 𝒪.obj (op V)) (s : M.obj (op V))
    (t : N.obj (op V)), app V hV (r • s) t = r • app V hV s t
  /-- Linearity over `𝒪(V)` in the second variable. -/
  map_smul_right : ∀ (V : Opens X) (hV : V ≤ U) (r : 𝒪.obj (op V)) (s : M.obj (op V))
    (t : N.obj (op V)), app V hV s (r • t) = r • app V hV s t
  /-- Compatibility with the restriction maps of `M`, `N` and `P`. -/
  naturality : ∀ {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V) (s : M.obj (op V))
    (t : N.obj (op V)), app W (hWV.trans hV) (M.resLE hWV s) (N.resLE hWV t)
      = P.resLE hWV (app V hV s t)

namespace LocalBilinearMap

variable {M N P : PresheafOfModules.{u} 𝒪}

/-- A local bilinear map is additive in its first variable. -/
theorem app_add_left {U : Opens X} (g : LocalBilinearMap M N P U) (V : Opens X) (hV : V ≤ U)
    (s s' : M.obj (op V)) (t : N.obj (op V)) :
    g.app V hV (s + s') t = g.app V hV s t + g.app V hV s' t := by
  rw [map_add]; rfl

/-- A local bilinear map is additive in its second variable. -/
theorem app_add_right {U : Opens X} (g : LocalBilinearMap M N P U) (V : Opens X) (hV : V ≤ U)
    (s : M.obj (op V)) (t t' : N.obj (op V)) :
    g.app V hV s (t + t') = g.app V hV s t + g.app V hV s t' :=
  map_add (g.app V hV s) t t'

variable {ι : Type u} {U : ι → Opens X}

/-! ### The local values of a pair of sections -/

/-- The local value of the glued bilinear map at a pair of sections over `V`: the value of the
`i`-th local bilinear map at the restrictions of the two sections to `V ⊓ U i`. -/
noncomputable def localValue (f : ∀ i, LocalBilinearMap M N P (U i)) {V : Opens X}
    (s : M.obj (op V)) (t : N.obj (op V)) (i : ι) : P.obj (op (V ⊓ U i)) :=
  (f i).app (V ⊓ U i) inf_le_right (M.resLE (inf_le_left : V ⊓ U i ≤ V) s)
    (N.resLE (inf_le_left : V ⊓ U i ≤ V) t)

/-- The local value is additive in its first variable. -/
theorem localValue_add_left (f : ∀ i, LocalBilinearMap M N P (U i)) {V : Opens X}
    (s s' : M.obj (op V)) (t : N.obj (op V)) (i : ι) :
    localValue f (s + s') t i = localValue f s t i + localValue f s' t i := by
  rw [localValue, localValue, localValue, map_add (M.resLE (inf_le_left : V ⊓ U i ≤ V)) s s',
    (f i).app_add_left]

/-- The local value is additive in its second variable. -/
theorem localValue_add_right (f : ∀ i, LocalBilinearMap M N P (U i)) {V : Opens X}
    (s : M.obj (op V)) (t t' : N.obj (op V)) (i : ι) :
    localValue f s (t + t') i = localValue f s t i + localValue f s t' i := by
  rw [localValue, localValue, localValue, map_add (N.resLE (inf_le_left : V ⊓ U i ≤ V)) t t',
    (f i).app_add_right]

/-- The local value is semilinear in its first variable. -/
theorem localValue_smul_left (f : ∀ i, LocalBilinearMap M N P (U i)) {V : Opens X}
    (r : 𝒪.obj (op V)) (s : M.obj (op V)) (t : N.obj (op V)) (i : ι) :
    localValue f (r • s) t i
      = (𝒪.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op).hom r • localValue f s t i := by
  rw [localValue, localValue, map_smulₛₗ (M.resLE (inf_le_left : V ⊓ U i ≤ V)) r s,
    (f i).map_smul_left]

/-- The local value is semilinear in its second variable. -/
theorem localValue_smul_right (f : ∀ i, LocalBilinearMap M N P (U i)) {V : Opens X}
    (r : 𝒪.obj (op V)) (s : M.obj (op V)) (t : N.obj (op V)) (i : ι) :
    localValue f s (r • t) i
      = (𝒪.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op).hom r • localValue f s t i := by
  rw [localValue, localValue, map_smulₛₗ (N.resLE (inf_le_left : V ⊓ U i ≤ V)) r t,
    (f i).map_smul_right]

/-- The local values of a pair of sections are compatible on the overlaps: on an open contained
in both `V ⊓ U i` and `V ⊓ U j` both are computed from the two sections by a single restriction
followed by the common value of the two local bilinear maps there. -/
theorem resLE_localValue_eq (f : ∀ i, LocalBilinearMap M N P (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    {V : Opens X} (s : M.obj (op V)) (t : N.obj (op V)) (i j : ι) {Z : Opens X}
    (hi : Z ≤ V ⊓ U i) (hj : Z ≤ V ⊓ U j) :
    P.resLE hi (localValue f s t i) = P.resLE hj (localValue f s t j) := by
  rw [localValue, localValue, ← (f i).naturality inf_le_right hi,
    ← (f j).naturality inf_le_right hj, M.resLE_resLE, M.resLE_resLE, N.resLE_resLE,
    N.resLE_resLE, hf i j Z (hi.trans inf_le_right) (hj.trans inf_le_right)]

/-! ### The glued bilinear map -/

variable (hU : ⨆ i, U i = ⊤)
  (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf)
  (f : ∀ i, LocalBilinearMap M N P (U i))
  (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
    (f i).app V hVi = (f j).app V hVj)

/-- The glued value at a pair of sections over `V`: the unique section of `P` over `V` whose
restriction to each `V ⊓ U i` is the corresponding local value. -/
noncomputable def gluedValue (V : Opens X) (s : M.obj (op V)) (t : N.obj (op V)) :
    P.obj (op V) :=
  (existsUnique_gluing_of_isSheafPresheaf hP (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) (localValue f s t)
    (fun k l => resLE_localValue_eq f hf s t k l inf_le_left inf_le_right)).choose

/-- The defining property of `TopCat.Sheaf.LocalBilinearMap.gluedValue`: it restricts to the
local values. -/
theorem resLE_gluedValue (V : Opens X) (s : M.obj (op V)) (t : N.obj (op V)) (i : ι) :
    P.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValue hU hP f hf V s t) = localValue f s t i :=
  (existsUnique_gluing_of_isSheafPresheaf hP (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) (localValue f s t)
    (fun k l => resLE_localValue_eq f hf s t k l inf_le_left inf_le_right)).choose_spec.1 i

/-- `TopCat.Sheaf.LocalBilinearMap.gluedValue` is characterised by its defining property. -/
theorem eq_gluedValue {V : Opens X} {s : M.obj (op V)} {t : N.obj (op V)} (y : P.obj (op V))
    (hy : ∀ i, P.resLE (inf_le_left : V ⊓ U i ≤ V) y = localValue f s t i) :
    y = gluedValue hU hP f hf V s t :=
  eq_of_locally_eq_of_isSheafPresheaf hP (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) fun i => (hy i).trans (resLE_gluedValue hU hP f hf V s t i).symm

/-- The glued value is additive in its first variable. -/
theorem gluedValue_add_left {V : Opens X} (s s' : M.obj (op V)) (t : N.obj (op V)) :
    gluedValue hU hP f hf V (s + s') t
      = gluedValue hU hP f hf V s t + gluedValue hU hP f hf V s' t :=
  (eq_gluedValue hU hP f hf _ fun i => by
    rw [map_add (P.resLE (inf_le_left : V ⊓ U i ≤ V)), resLE_gluedValue hU hP f hf V s t i,
      resLE_gluedValue hU hP f hf V s' t i, localValue_add_left f s s' t i]).symm

/-- The glued value is additive in its second variable. -/
theorem gluedValue_add_right {V : Opens X} (s : M.obj (op V)) (t t' : N.obj (op V)) :
    gluedValue hU hP f hf V s (t + t')
      = gluedValue hU hP f hf V s t + gluedValue hU hP f hf V s t' :=
  (eq_gluedValue hU hP f hf _ fun i => by
    rw [map_add (P.resLE (inf_le_left : V ⊓ U i ≤ V)), resLE_gluedValue hU hP f hf V s t i,
      resLE_gluedValue hU hP f hf V s t' i, localValue_add_right f s t t' i]).symm

/-- The glued value is `𝒪(V)`-linear in its first variable. -/
theorem gluedValue_smul_left {V : Opens X} (r : 𝒪.obj (op V)) (s : M.obj (op V))
    (t : N.obj (op V)) :
    gluedValue hU hP f hf V (r • s) t = r • gluedValue hU hP f hf V s t :=
  (eq_gluedValue hU hP f hf _ fun i => by
    rw [map_smulₛₗ (P.resLE (inf_le_left : V ⊓ U i ≤ V)) r,
      resLE_gluedValue hU hP f hf V s t i, localValue_smul_left f r s t i]).symm

/-- The glued value is `𝒪(V)`-linear in its second variable. -/
theorem gluedValue_smul_right {V : Opens X} (r : 𝒪.obj (op V)) (s : M.obj (op V))
    (t : N.obj (op V)) :
    gluedValue hU hP f hf V s (r • t) = r • gluedValue hU hP f hf V s t :=
  (eq_gluedValue hU hP f hf _ fun i => by
    rw [map_smulₛₗ (P.resLE (inf_le_left : V ⊓ U i ≤ V)) r,
      resLE_gluedValue hU hP f hf V s t i, localValue_smul_right f r s t i]).symm

/-- The glued value commutes with the restriction maps. -/
theorem gluedValue_resLE {V W : Opens X} (hWV : W ≤ V) (s : M.obj (op V)) (t : N.obj (op V)) :
    gluedValue hU hP f hf W (M.resLE hWV s) (N.resLE hWV t)
      = P.resLE hWV (gluedValue hU hP f hf V s t) := by
  refine (eq_gluedValue hU hP f hf _ fun i => ?_).symm
  have hk : W ⊓ U i ≤ V ⊓ U i := inf_le_inf_right (U i) hWV
  rw [resLE_inf_le_left_resLE hWV, resLE_gluedValue hU hP f hf V s t i, localValue, localValue,
    ← (f i).naturality inf_le_right hk, M.resLE_resLE, M.resLE_resLE, N.resLE_resLE,
    N.resLE_resLE]

/-- On an open contained in a member of the covering, the glued value is the value of that
member's own local bilinear map. -/
theorem gluedValue_eq_app {i : ι} {V : Opens X} (hV : V ≤ U i) (s : M.obj (op V))
    (t : N.obj (op V)) :
    gluedValue hU hP f hf V s t = (f i).app V hV s t :=
  (eq_gluedValue hU hP f hf _ fun j => by
    rw [← (f i).naturality hV (inf_le_left : V ⊓ U j ≤ V), localValue,
      hf i j (V ⊓ U j) (inf_le_left.trans hV) inf_le_right]).symm

/-- **The glued `𝒪`-bilinear map of presheaves of `𝒪`-modules.** -/
noncomputable def gluedBilinearMap : Stacks.BilinearMap M N P where
  app Y := AddMonoidHom.mk'
    (fun s => AddMonoidHom.mk' (fun t => gluedValue hU hP f hf Y.unop s t)
      (gluedValue_add_right hU hP f hf s))
    (fun s s' => AddMonoidHom.ext (gluedValue_add_left hU hP f hf s s'))
  map_smul_left _Y r s t := gluedValue_smul_left hU hP f hf r s t
  map_smul_right _Y r s t := gluedValue_smul_right hU hP f hf r s t
  naturality {_Y _Z} g s t := by
    rw [show g = (homOfLE (Quiver.Hom.unop g).le).op from Subsingleton.elim _ _]
    exact (gluedValue_resLE hU hP f hf (Quiver.Hom.unop g).le s t).symm

/-- The glued bilinear map restricts to the `i`-th local bilinear map over every open contained
in `U i`. -/
theorem gluedBilinearMap_app (i : ι) (V : Opens X) (hV : V ≤ U i) (s : M.obj (op V))
    (t : N.obj (op V)) :
    (gluedBilinearMap hU hP f hf).app (op V) s t = (f i).app V hV s t :=
  gluedValue_eq_app hU hP f hf hV s t

end LocalBilinearMap

/-- A bilinear map of presheaves of `𝒪`-modules commutes with restriction along inclusions of
opens. This is `Stacks.BilinearMap.naturality` at an inclusion, read through
`PresheafOfModules.resLE`. -/
theorem bilinear_app_resLE {M N P : PresheafOfModules.{u} 𝒪} (β : Stacks.BilinearMap M N P)
    {V W : Opens X} (h : W ≤ V) (s : M.obj (op V)) (t : N.obj (op V)) :
    β.app (op W) (M.resLE h s) (N.resLE h t) = P.resLE h (β.app (op V) s t) :=
  (β.naturality (homOfLE h).op s t).symm

/-- The uniqueness half, on its own: a bilinear map of presheaves of `𝒪`-modules into a sheaf is
determined by its restrictions to a covering. No compatibility hypothesis on the local data is
needed, and it enters only through the equations the two bilinear maps are asserted to
satisfy. -/
theorem eq_bilinearMap_of_restrict {ι : Type u} {U : ι → Opens X} (hU : ⨆ i, U i = ⊤)
    {M N P : PresheafOfModules.{u} 𝒪}
    (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf)
    (g : ∀ (i : ι) (V : Opens X), V ≤ U i → M.obj (op V) →+ N.obj (op V) →+ P.obj (op V))
    {β β' : Stacks.BilinearMap M N P}
    (hβ : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i) (s : M.obj (op V)) (t : N.obj (op V)),
      β.app (op V) s t = g i V hV s t)
    (hβ' : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i) (s : M.obj (op V)) (t : N.obj (op V)),
      β'.app (op V) s t = g i V hV s t) :
    β = β' := by
  refine Stacks.BilinearMap.ext fun Y s t => ?_
  refine eq_of_locally_eq_of_isSheafPresheaf hP (fun i => Y.unop ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU Y.unop) fun i => ?_
  rw [← bilinear_app_resLE β (inf_le_left : Y.unop ⊓ U i ≤ Y.unop) s t,
    ← bilinear_app_resLE β' (inf_le_left : Y.unop ⊓ U i ≤ Y.unop) s t,
    hβ i (Y.unop ⊓ U i) inf_le_right, hβ' i (Y.unop ⊓ U i) inf_le_right]

/-- **Bilinear maps of sheaves of `𝒪`-modules glue over an open covering.** Let `𝒪` be a presheaf
of rings on a topological space `X`, let `U : ι → Opens X` be an open covering of `X`, let `M` and
`N` be presheaves of `𝒪`-modules and let `P` be a sheaf of `𝒪`-modules. Local `𝒪`-bilinear maps
`M × N → P` on the members of the covering which agree on all overlaps glue to a unique
`𝒪`-bilinear map `M × N → P` restricting to each of them.

The compatibility hypothesis is stated over every open `V` contained in both `U i` and `U j`, so
the overlaps are not required to belong to the covering family. -/
theorem existsUnique_bilinearMap_of_localBilinearMap {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (M N P : PresheafOfModules.{u} 𝒪)
    (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) P.presheaf)
    (f : ∀ i, LocalBilinearMap M N P (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! β : Stacks.BilinearMap M N P, ∀ (i : ι) (V : Opens X) (hV : V ≤ U i)
      (s : M.obj (op V)) (t : N.obj (op V)), β.app (op V) s t = (f i).app V hV s t :=
  ⟨LocalBilinearMap.gluedBilinearMap hU hP f hf,
    LocalBilinearMap.gluedBilinearMap_app hU hP f hf,
    fun _ hβ => eq_bilinearMap_of_restrict hU hP (fun i V hV => (f i).app V hV) hβ
      (LocalBilinearMap.gluedBilinearMap_app hU hP f hf)⟩

/-! ### Local global sections of a presheaf of `𝒪`-modules -/

/-- A *global section of a presheaf of `𝒪`-modules over an open subset `U` of `X`*: a section
over every open `V` of `X` contained in `U`, compatible with all restriction maps.

This is recorded in the style of `TopCat.Sheaf.LocalModuleHom`, for the same reason: an overlap
of two members of a covering is then a single open of `X`. -/
structure LocalSectionData (M : PresheafOfModules.{u} 𝒪) (U : Opens X) where
  /-- The section over an open `V ≤ U`. -/
  app : ∀ (V : Opens X), V ≤ U → M.obj (op V)
  /-- Compatibility with the restriction maps of `M`. -/
  naturality : ∀ {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V),
    M.resLE hWV (app V hV) = app W (hWV.trans hV)

namespace LocalSectionData

variable {M : PresheafOfModules.{u} 𝒪} {ι : Type u} {U : ι → Opens X}

/-- The local value of the glued section over `V`: the `i`-th local section over `V ⊓ U i`. -/
def localValue (f : ∀ i, LocalSectionData M (U i)) (V : Opens X) (i : ι) :
    M.obj (op (V ⊓ U i)) :=
  (f i).app (V ⊓ U i) inf_le_right

/-- The local values are compatible on the overlaps. -/
theorem resLE_localValue_eq (f : ∀ i, LocalSectionData M (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    (V : Opens X) (i j : ι) {Z : Opens X} (hi : Z ≤ V ⊓ U i) (hj : Z ≤ V ⊓ U j) :
    M.resLE hi (localValue f V i) = M.resLE hj (localValue f V j) := by
  rw [localValue, localValue, (f i).naturality inf_le_right hi,
    (f j).naturality inf_le_right hj, hf i j Z (hi.trans inf_le_right) (hj.trans inf_le_right)]

variable (hU : ⨆ i, U i = ⊤)
  (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
  (f : ∀ i, LocalSectionData M (U i))
  (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
    (f i).app V hVi = (f j).app V hVj)

/-- The glued section over `V`: the unique section of `M` over `V` whose restriction to each
`V ⊓ U i` is the corresponding local value. -/
noncomputable def gluedValue (V : Opens X) : M.obj (op V) :=
  (existsUnique_gluing_of_isSheafPresheaf hM (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) (localValue f V)
    (fun k l => resLE_localValue_eq f hf V k l inf_le_left inf_le_right)).choose

/-- The defining property of `TopCat.Sheaf.LocalSectionData.gluedValue`. -/
theorem resLE_gluedValue (V : Opens X) (i : ι) :
    M.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValue hU hM f hf V) = localValue f V i :=
  (existsUnique_gluing_of_isSheafPresheaf hM (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) (localValue f V)
    (fun k l => resLE_localValue_eq f hf V k l inf_le_left inf_le_right)).choose_spec.1 i

/-- `TopCat.Sheaf.LocalSectionData.gluedValue` is characterised by its defining property. -/
theorem eq_gluedValue {V : Opens X} (y : M.obj (op V))
    (hy : ∀ i, M.resLE (inf_le_left : V ⊓ U i ≤ V) y = localValue f V i) :
    y = gluedValue hU hM f hf V :=
  eq_of_locally_eq_of_isSheafPresheaf hM (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) fun i => (hy i).trans (resLE_gluedValue hU hM f hf V i).symm

/-- The glued sections are compatible with the restriction maps. -/
theorem gluedValue_resLE {V W : Opens X} (hWV : W ≤ V) :
    M.resLE hWV (gluedValue hU hM f hf V) = gluedValue hU hM f hf W := by
  refine eq_gluedValue hU hM f hf _ fun i => ?_
  have hk : W ⊓ U i ≤ V ⊓ U i := inf_le_inf_right (U i) hWV
  rw [resLE_inf_le_left_resLE hWV, resLE_gluedValue hU hM f hf V i, localValue, localValue,
    (f i).naturality inf_le_right hk]

/-- On an open contained in a member of the covering, the glued section is that member's own
local section. -/
theorem gluedValue_eq_app {i : ι} {V : Opens X} (hV : V ≤ U i) :
    gluedValue hU hM f hf V = (f i).app V hV :=
  (eq_gluedValue hU hM f hf _ fun j => by
    rw [localValue, (f i).naturality hV (inf_le_left : V ⊓ U j ≤ V),
      hf i j (V ⊓ U j) (inf_le_left.trans hV) inf_le_right]).symm

/-- **The glued global section of a presheaf of `𝒪`-modules.** -/
noncomputable def gluedSections : M.sections :=
  M.sectionsMk (fun Y => gluedValue hU hM f hf Y.unop) (by
    intro _Y _Z g
    rw [show g = (homOfLE (Quiver.Hom.unop g).le).op from Subsingleton.elim _ _]
    exact gluedValue_resLE hU hM f hf (Quiver.Hom.unop g).le)

/-- The glued global section evaluates, over an open contained in `U i`, to the `i`-th local
section there. -/
theorem gluedSections_eval (i : ι) (V : Opens X) (hV : V ≤ U i) :
    (gluedSections hU hM f hf).eval (op V) = (f i).app V hV :=
  gluedValue_eq_app hU hM f hf hV

end LocalSectionData

/-- The uniqueness half for global sections, on its own: a global section of a sheaf of
`𝒪`-modules is determined by its values over the members of a covering. -/
theorem eq_sections_of_restrict {ι : Type u} {U : ι → Opens X} (hU : ⨆ i, U i = ⊤)
    {M : PresheafOfModules.{u} 𝒪}
    (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
    (g : ∀ (i : ι) (V : Opens X), V ≤ U i → M.obj (op V)) {s s' : M.sections}
    (hs : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), s.eval (op V) = g i V hV)
    (hs' : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), s'.eval (op V) = g i V hV) :
    s = s' := by
  refine PresheafOfModules.sections_ext s s' fun Y => ?_
  refine eq_of_locally_eq_of_isSheafPresheaf hM (fun i => Y.unop ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU Y.unop) fun i => ?_
  have h : ∀ t : M.sections, M.resLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop) (t.val Y)
      = t.eval (op (Y.unop ⊓ U i)) := fun t =>
    PresheafOfModules.sections_property t (homOfLE (inf_le_left : Y.unop ⊓ U i ≤ Y.unop)).op
  rw [h s, h s', hs i (Y.unop ⊓ U i) inf_le_right, hs' i (Y.unop ⊓ U i) inf_le_right]

/-- **Global sections of a sheaf of `𝒪`-modules glue over an open covering.** Let `𝒪` be a
presheaf of rings on a topological space `X`, let `U : ι → Opens X` be an open covering of `X`
and let `M` be a sheaf of `𝒪`-modules. Local global sections of `M` on the members of the
covering which agree on all overlaps glue to a unique global section of `M` restricting to each
of them.

The compatibility hypothesis is stated over every open contained in two members of the covering,
so the overlaps are not required to belong to the covering family. -/
theorem existsUnique_sections_of_localSectionData {ι : Type u} (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) (M : PresheafOfModules.{u} 𝒪)
    (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
    (f : ∀ i, LocalSectionData M (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! s : M.sections, ∀ (i : ι) (V : Opens X) (hV : V ≤ U i),
      s.eval (op V) = (f i).app V hV :=
  ⟨LocalSectionData.gluedSections hU hM f hf, LocalSectionData.gluedSections_eval hU hM f hf,
    fun _ hs => eq_sections_of_restrict hU hM (fun i V hV => (f i).app V hV) hs
      (LocalSectionData.gluedSections_eval hU hM f hf)⟩

end TopCat.Sheaf

end
