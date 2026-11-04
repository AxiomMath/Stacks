module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleBilinearGluing

/-!
# Glueing a multiplication and a unit on sheaves of modules on a scheme

`Stacks.AlgebraicGeometry.ModuleHomGlue` glues *morphisms* of sheaves of modules on a scheme over
an open cover. An algebra structure on a sheaf of modules consists of two further kinds of datum,
and neither is a morphism: a **multiplication**, which is an `𝒪_X`-bilinear map, and a **unit**,
which is a global section. This file glues both.

Everything is stated for an arbitrary open cover of an arbitrary scheme: **no quasi-coherence, no
affineness and no finiteness hypothesis appears**, and only the target has to be a sheaf, which it
is by definition of `AlgebraicGeometry.Scheme.Modules`.

## What was already here

The sheaf-theoretic content is *not* proved here.
`TopCat.Sheaf.existsUnique_bilinearMap_of_localBilinearMap` and
`TopCat.Sheaf.existsUnique_sections_of_localSectionData` in
`StacksFrontier/Topology/Sheaves/Glueing/OModuleBilinearGluing.lean` already glue bilinear maps and
global sections of presheaves of `𝒪`-modules over an open cover of a topological space, for an
arbitrary presheaf of rings `𝒪`. This file is the transport of those statements to
`AlgebraicGeometry.Scheme.Modules`, which is `SheafOfModules X.ringCatSheaf`: the `𝒪` there is
`X.ringCatSheaf.obj` and the sheaf hypothesis on the target is `P.isSheaf`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.localBilinearMapOfApp`: local multiplication data
  on an open `U` of `X`, built from a family of maps `Γ(M, V) → Γ(N, V) → Γ(P, V)` for the opens
  `V ≤ U`, their biadditivity, their `Γ(X, V)`-bilinearity and their compatibility with
  restriction. This is the `Γ`-idiom shape of `TopCat.Sheaf.LocalBilinearMap`.
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.localSectionDataOfApp`: the same for local unit
  data, i.e. for `TopCat.Sheaf.LocalSectionData`.
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap` and
  `gluedSections`: **the glued multiplication and the glued unit**, as a
  `SheafOfModules.BilinearMap` and an element of `SheafOfModules.sections`. These are honest
  definitions with a body, not data chosen from an existence statement, so a graded-algebra
  structure can be built from them and its laws proved.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.existsUnique_bilinearMap_of_cover`: **bilinear
  maps of sheaves of modules on a scheme glue over an open cover.**
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.existsUnique_sections_of_cover`: **global sections
  of a sheaf of modules on a scheme glue over an open cover.**
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap_app` and `gluedSections_eval`:
  over an open contained in a member of the cover, the glued multiplication and unit are that
  member's own. These are the equations a consumer checking an algebra law locally needs.
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.bilinearMap_ext_of_cover` and
  `sections_ext_of_cover`: two bilinear maps, respectively two global sections, agreeing over the
  members of a cover are equal. This is the separation half of their locality.
* `Stacks.AlgebraicGeometry.ModuleBilinearGlue.heq_of_cover`: a *heterogeneous* equation between
  sections of two members of a family of sheaves of modules at propositionally equal indices may
  be checked over the members of a cover. This is what reduces an associativity or unit law on
  glued data to the same law on each chart, those laws being heterogeneous because the degrees
  `(i + j) + k` and `i + (j + k)` are not definitionally equal.

## Implementation notes

The compatibility hypotheses are stated over *every* open `V` of `X` contained in both `U i` and
`U j`, inherited from `TopCat.Sheaf.LocalBilinearMap`: an overlap of two members of the cover is a
single open of `X` and is never required to belong to the covering family. The index of the cover
lands in `Type u`, the same universe as the scheme, which is what the underlying gluing statement
asks for.

`SheafOfModules.BilinearMap M N P` is an abbreviation for `Stacks.BilinearMap M.val N.val P.val`,
so the statements below are literally the topological ones with `𝒪 := X.ringCatSheaf.obj`; the
`SheafOfModules` spelling is used because that is the type the `mul` field of
`SheafOfModules.GradedAlgebra` has.

As in `Stacks.AlgebraicGeometry.ModuleHomGlue`, the scalar rings are the sections of the structure
sheaf read in `RingCat`, since that is where the module structures on the sections of a
`PresheafOfModules` are registered, but the `Γ(X, V)` spelling elaborates against them.

## No tag is claimed

No `stacks` attribute is attached. This is infrastructure, not an assertion of any tag. It is one
of the two named inputs to the `algebra` field of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` — the other being the glued homogeneous
pieces, `Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` — but that field is not
reached from here: producing it also needs the chart comparisons of the glued twists to carry the
canonical product of absolute twist sections to one another, which nothing in this repository
proves.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleBilinearGlue

universe v u

variable {X : Scheme.{u}}

/-! ### Local multiplication data, given on sections -/

/-- **Local multiplication data on an open `U`, given on sections.** A family of maps
`Γ(M, V) → Γ(N, V) → Γ(P, V)` indexed by the opens `V ≤ U`, biadditive, linear over `Γ(X, V)` in
each variable and compatible with the restriction maps, is the same thing as an `𝒪_X|_U`-bilinear
map `M|_U × N|_U → P|_U`; it is recorded as a `TopCat.Sheaf.LocalBilinearMap`, which indexes it by
the opens of `X` inside `U` rather than by the opens of the subspace. -/
public def localBilinearMapOfApp {M N P : X.Modules} (U : X.Opens)
    (g : ∀ V : X.Opens, V ≤ U → Γ(M, V) → Γ(N, V) → Γ(P, V))
    (hadd_left : ∀ (V : X.Opens) (hV : V ≤ U) (s s' : Γ(M, V)) (t : Γ(N, V)),
      g V hV (s + s') t = g V hV s t + g V hV s' t)
    (hadd_right : ∀ (V : X.Opens) (hV : V ≤ U) (s : Γ(M, V)) (t t' : Γ(N, V)),
      g V hV s (t + t') = g V hV s t + g V hV s t')
    (hsmul_left : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)) (t : Γ(N, V)),
      g V hV (r • s) t = r • g V hV s t)
    (hsmul_right : ∀ (V : X.Opens) (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)) (t : Γ(N, V)),
      g V hV s (r • t) = r • g V hV s t)
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(M, V)) (t : Γ(N, V)),
      g W (hWV.trans hV) (M.val.resLE hWV s) (N.val.resLE hWV t)
        = P.val.resLE hWV (g V hV s t)) :
    TopCat.Sheaf.LocalBilinearMap M.val N.val P.val U where
  app V hV :=
    AddMonoidHom.mk'
      (fun s => AddMonoidHom.mk' (fun t => g V hV s t) (hadd_right V hV s))
      (fun s s' => AddMonoidHom.ext (hadd_left V hV s s'))
  map_smul_left V hV r s t := hsmul_left V hV r s t
  map_smul_right V hV r s t := hsmul_right V hV r s t
  naturality hV hWV s t := hres _ _ hV hWV s t

/-- The local multiplication data cut out of a global bilinear map by forgetting everything
outside `U`. This direction uses no sheaf condition: it is just the naturality of `β`. -/
public def localBilinearMapOfBilinearMap {M N P : X.Modules}
    (β : SheafOfModules.BilinearMap M N P) (U : X.Opens) :
    TopCat.Sheaf.LocalBilinearMap M.val N.val P.val U where
  app V _ := β.app (op V)
  map_smul_left V _ r s t := β.map_smul_left (op V) r s t
  map_smul_right V _ r s t := β.map_smul_right (op V) r s t
  naturality _ hWV s t := TopCat.Sheaf.bilinear_app_resLE β hWV s t

/-! ### Local unit data, given on sections -/

/-- **Local unit data on an open `U`, given on sections.** A section of `M` over every open
`V ≤ U`, compatible with the restriction maps. -/
public def localSectionDataOfApp {M : X.Modules} (U : X.Opens)
    (g : ∀ V : X.Opens, V ≤ U → Γ(M, V))
    (hres : ∀ (V W : X.Opens) (hV : V ≤ U) (hWV : W ≤ V),
      M.val.resLE hWV (g V hV) = g W (hWV.trans hV)) :
    TopCat.Sheaf.LocalSectionData M.val U where
  app := g
  naturality hV hWV := hres _ _ hV hWV

/-- The local unit data cut out of a global section by forgetting everything outside `U`. -/
public def localSectionDataOfSections {M : X.Modules} (s : M.sections) (U : X.Opens) :
    TopCat.Sheaf.LocalSectionData M.val U where
  app V _ := s.eval (op V)
  naturality _ hWV := PresheafOfModules.sections_property s (homOfLE hWV).op

/-! ### The glued multiplication -/

variable {M N P : X.Modules} {ι : Type u} {U : ι → X.Opens}

/-- **The glued multiplication**: an `𝒪_X`-bilinear map `M × N → P` on the whole of `X`, built
from local bilinear maps on the members of an open cover agreeing on all overlaps.

This is a definition with a body, so an algebra law for it can be checked locally through
`Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap_app`. -/
public def gluedBilinearMap (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalBilinearMap M.val N.val P.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    SheafOfModules.BilinearMap M N P :=
  TopCat.Sheaf.LocalBilinearMap.gluedBilinearMap hU P.isSheaf f hf

/-- The restriction of a value of the glued multiplication is its value at the restrictions. This
is `Stacks.BilinearMap.naturality` for the glued object, and it is what pushes a restriction
inside an algebra law. -/
public theorem resLE_gluedBilinearMap_app (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalBilinearMap M.val N.val P.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    {V W : X.Opens} (hWV : W ≤ V) (s : Γ(M, V)) (t : Γ(N, V)) :
    P.val.resLE hWV ((gluedBilinearMap hU f hf).app (op V) s t)
      = (gluedBilinearMap hU f hf).app (op W) (M.val.resLE hWV s) (N.val.resLE hWV t) :=
  (TopCat.Sheaf.bilinear_app_resLE (gluedBilinearMap hU f hf) hWV s t).symm

/-- Over an open contained in a member of the cover, the glued multiplication is that member's
own. -/
public theorem gluedBilinearMap_app (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalBilinearMap M.val N.val P.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    (i : ι) (V : X.Opens) (hV : V ≤ U i) (s : Γ(M, V)) (t : Γ(N, V)) :
    (gluedBilinearMap hU f hf).app (op V) s t = (f i).app V hV s t :=
  TopCat.Sheaf.LocalBilinearMap.gluedBilinearMap_app hU P.isSheaf f hf i V hV s t

/-- **Two bilinear maps of sheaves of modules agreeing over the members of an open cover are
equal.** This is the separation half of the locality of bilinear maps, and it is what reduces an
associativity or unit law for a glued multiplication to the same law on each member of the
cover. -/
public theorem bilinearMap_ext_of_cover (hU : ⨆ i, U i = ⊤)
    {β β' : SheafOfModules.BilinearMap M N P}
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → ∀ (s : Γ(M, V)) (t : Γ(N, V)),
      β.app (op V) s t = β'.app (op V) s t) :
    β = β' :=
  TopCat.Sheaf.eq_bilinearMap_of_restrict hU P.isSheaf (fun _ V _ => β'.app (op V))
    (fun i V hV s t => h i V hV s t) (fun _ _ _ _ _ => rfl)

/-- **Bilinear maps of sheaves of modules on a scheme glue over an open cover.** Let `U` be an
open cover of a scheme `X`, let `M`, `N` be sheaves of `𝒪_X`-modules and let `P` be one too. A
family of local `𝒪_X`-bilinear maps `M|_{U i} × N|_{U i} → P|_{U i}` which agree on every open
contained in two members of the cover comes from exactly one bilinear map `M × N → P`.

Only the target's sheaf condition is used, and it is part of the definition of
`AlgebraicGeometry.Scheme.Modules`; there is no hypothesis on `X`, on the cover or on `M`, `N` and
`P` beyond that. -/
public theorem existsUnique_bilinearMap_of_cover (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalBilinearMap M.val N.val P.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! β : SheafOfModules.BilinearMap M N P, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i)
      (s : Γ(M, V)) (t : Γ(N, V)), β.app (op V) s t = (f i).app V hV s t :=
  TopCat.Sheaf.existsUnique_bilinearMap_of_localBilinearMap U hU M.val N.val P.val P.isSheaf f hf

/-- **The gluing of bilinear maps of sheaves of modules, on sections.** The same statement as
`Stacks.AlgebraicGeometry.ModuleBilinearGlue.existsUnique_bilinearMap_of_cover`, with the local
data given as maps on sections which are biadditive, bilinear and compatible with restriction.
This is the form a consumer supplies. -/
public theorem existsUnique_bilinearMap_of_cover_app (hU : ⨆ i, U i = ⊤)
    (g : ∀ (i : ι) (V : X.Opens), V ≤ U i → Γ(M, V) → Γ(N, V) → Γ(P, V))
    (hadd_left : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (s s' : Γ(M, V)) (t : Γ(N, V)),
      g i V hV (s + s') t = g i V hV s t + g i V hV s' t)
    (hadd_right : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (s : Γ(M, V)) (t t' : Γ(N, V)),
      g i V hV s (t + t') = g i V hV s t + g i V hV s t')
    (hsmul_left : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (r : Γ(X, V)) (s : Γ(M, V))
      (t : Γ(N, V)), g i V hV (r • s) t = r • g i V hV s t)
    (hsmul_right : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i) (r : Γ(X, V)) (s : Γ(M, V))
      (t : Γ(N, V)), g i V hV s (r • t) = r • g i V hV s t)
    (hres : ∀ (i : ι) (V W : X.Opens) (hV : V ≤ U i) (hWV : W ≤ V) (s : Γ(M, V)) (t : Γ(N, V)),
      g i W (hWV.trans hV) (M.val.resLE hWV s) (N.val.resLE hWV t)
        = P.val.resLE hWV (g i V hV s t))
    (hg : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j) (s : Γ(M, V)) (t : Γ(N, V)),
      g i V hVi s t = g j V hVj s t) :
    ∃! β : SheafOfModules.BilinearMap M N P, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i)
      (s : Γ(M, V)) (t : Γ(N, V)), β.app (op V) s t = g i V hV s t :=
  existsUnique_bilinearMap_of_cover hU
    (fun i => localBilinearMapOfApp (U i) (g i) (hadd_left i) (hadd_right i) (hsmul_left i)
      (hsmul_right i) (hres i))
    (fun i j V hVi hVj => AddMonoidHom.ext fun s =>
      AddMonoidHom.ext fun t => hg i j V hVi hVj s t)

/-! ### The glued unit -/

/-- **The glued unit**: a global section of `M` on the whole of `X`, built from local sections on
the members of an open cover agreeing on all overlaps. -/
public def gluedSections (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalSectionData M.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    M.sections :=
  TopCat.Sheaf.LocalSectionData.gluedSections hU M.isSheaf f hf

/-- Over an open contained in a member of the cover, the glued unit is that member's own local
section. -/
public theorem gluedSections_eval (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalSectionData M.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    (gluedSections hU f hf).eval (op V) = (f i).app V hV :=
  TopCat.Sheaf.LocalSectionData.gluedSections_eval hU M.isSheaf f hf i V hV

/-! ### Heterogeneous laws, checked on a cover -/

/-- **A heterogeneous equation between sections of two sheaves of modules drawn from a family at
propositionally equal indices may be checked over the members of an open cover.**

This is the shape the three laws of a `SheafOfModules.GradedAlgebra` have: the two sides of
`mul_assoc` are sections of the pieces indexed by `(i + j) + k` and by `i + (j + k)`, and those of
the two unit laws of the pieces indexed by `0 + i` and `i`, respectively `i + 0` and `i`. So this
is what reduces an associativity or unit law for a glued multiplication to the same law on each
member of the cover, where the glued multiplication is the member's own by
`Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedBilinearMap_app`.

The index equality is substituted away before the sheaf condition is used, so no motive is ever
elaborated at a compound index. -/
public theorem heq_of_cover {Y : Type v} {F : Y → X.Modules} {a b : Y} (hab : a = b)
    {V : X.Opens} (s : Γ(F a, V)) (t : Γ(F b, V)) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i : ι, HEq ((F a).val.resLE (inf_le_left : V ⊓ U i ≤ V) s)
      ((F b).val.resLE (inf_le_left : V ⊓ U i ≤ V) t)) :
    HEq s t := by
  subst hab
  exact heq_of_eq (TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (F a).isSheaf
    (fun i => V ⊓ U i) (fun _ => inf_le_left) (TopCat.Sheaf.le_iSup_inf hU V)
    fun i => eq_of_heq (h i))

/-- **Two global sections of a sheaf of modules agreeing over the members of an open cover are
equal.** -/
public theorem sections_ext_of_cover (hU : ⨆ i, U i = ⊤) {s s' : M.sections}
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → s.eval (op V) = s'.eval (op V)) :
    s = s' :=
  TopCat.Sheaf.eq_sections_of_restrict hU M.isSheaf (fun _ V _ => s'.eval (op V))
    (fun i V hV => h i V hV) (fun _ _ _ => rfl)

/-- **Global sections of a sheaf of modules on a scheme glue over an open cover.** -/
public theorem existsUnique_sections_of_cover (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalSectionData M.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! s : M.sections, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i),
      s.eval (op V) = (f i).app V hV :=
  TopCat.Sheaf.existsUnique_sections_of_localSectionData U hU M.val M.isSheaf f hf

/-- **The gluing of global sections, on sections.** The same statement as
`Stacks.AlgebraicGeometry.ModuleBilinearGlue.existsUnique_sections_of_cover`, with the local data
given as sections compatible with restriction. -/
public theorem existsUnique_sections_of_cover_app (hU : ⨆ i, U i = ⊤)
    (g : ∀ (i : ι) (V : X.Opens), V ≤ U i → Γ(M, V))
    (hres : ∀ (i : ι) (V W : X.Opens) (hV : V ≤ U i) (hWV : W ≤ V),
      M.val.resLE hWV (g i V hV) = g i W (hWV.trans hV))
    (hg : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j), g i V hVi = g j V hVj) :
    ∃! s : M.sections, ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i), s.eval (op V) = g i V hV :=
  existsUnique_sections_of_cover hU
    (fun i => localSectionDataOfApp (U i) (g i) (hres i)) hg

/-- The restriction of the glued unit is the glued unit. -/
public theorem resLE_gluedSections_eval (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, TopCat.Sheaf.LocalSectionData M.val (U i))
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    {V W : X.Opens} (hWV : W ≤ V) :
    M.val.resLE hWV ((gluedSections hU f hf).eval (op V))
      = (gluedSections hU f hf).eval (op W) :=
  PresheafOfModules.sections_property (gluedSections hU f hf) (homOfLE hWV).op

/-! ### A sheaf of graded algebras, glued from local ones -/

section GradedAlgebra

variable {piece : ℤ → X.Modules}
  (hU : ⨆ i, U i = ⊤)
  (mulData : ∀ (i j : ℤ) (k : ι),
    TopCat.Sheaf.LocalBilinearMap (piece i).val (piece j).val (piece (i + j)).val (U k))
  (hmulData : ∀ (i j : ℤ) (k l : ι) (V : X.Opens) (hVk : V ≤ U k) (hVl : V ≤ U l),
    (mulData i j k).app V hVk = (mulData i j l).app V hVl)
  (oneData : ∀ k : ι, TopCat.Sheaf.LocalSectionData (piece 0).val (U k))
  (honeData : ∀ (k l : ι) (V : X.Opens) (hVk : V ≤ U k) (hVl : V ≤ U l),
    (oneData k).app V hVk = (oneData l).app V hVl)

/-- The glued multiplication in a pair of degrees. -/
public def gluedMul (i j : ℤ) :
    SheafOfModules.BilinearMap (piece i) (piece j) (piece (i + j)) :=
  gluedBilinearMap hU (mulData i j) (hmulData i j)

/-- Over an open contained in a member of the cover, the glued multiplication is that member's
own. -/
public theorem gluedMul_app (i j : ℤ) (m : ι) (V : X.Opens) (hV : V ≤ U m)
    (x : Γ(piece i, V)) (y : Γ(piece j, V)) :
    (gluedMul hU mulData hmulData i j).app (op V) x y = (mulData i j m).app V hV x y :=
  gluedBilinearMap_app hU (mulData i j) (hmulData i j) m V hV x y

/-- Pushing a restriction inside the glued multiplication. -/
public theorem resLE_gluedMul_app (i j : ℤ) {V W : X.Opens} (hWV : W ≤ V)
    (x : Γ(piece i, V)) (y : Γ(piece j, V)) :
    (piece (i + j)).val.resLE hWV ((gluedMul hU mulData hmulData i j).app (op V) x y)
      = (gluedMul hU mulData hmulData i j).app (op W)
        ((piece i).val.resLE hWV x) ((piece j).val.resLE hWV y) :=
  resLE_gluedBilinearMap_app hU (mulData i j) (hmulData i j) hWV x y

/-- The glued unit. -/
public def gluedOne : (piece 0).sections :=
  gluedSections hU oneData honeData

/-- Over an open contained in a member of the cover, the glued unit is that member's own. -/
public theorem gluedOne_eval (m : ι) (V : X.Opens) (hV : V ≤ U m) :
    (gluedOne hU oneData honeData).eval (op V) = (oneData m).app V hV :=
  gluedSections_eval hU oneData honeData m V hV

/-- Pushing a restriction inside the glued unit. -/
public theorem resLE_gluedOne_eval {V W : X.Opens} (hWV : W ≤ V) :
    (piece 0).val.resLE hWV ((gluedOne hU oneData honeData).eval (op V))
      = (gluedOne hU oneData honeData).eval (op W) :=
  resLE_gluedSections_eval hU oneData honeData hWV

/-- The restriction of a value of the glued multiplication to an open contained in a member of
the cover, computed by that member's own local multiplication. This is the one step the algebra
laws need, and it is stated in term form because the congruence motive of a rewrite is elaborated
at implicit transparency, which does not see through the semireducible
`AlgebraicGeometry.Scheme.Modules`. -/
public theorem resLE_gluedMul_app_eq (i j : ℤ) (m : ι) {V W : X.Opens} (hWV : W ≤ V)
    (hm : W ≤ U m) (x : Γ(piece i, V)) (y : Γ(piece j, V)) :
    (piece (i + j)).val.resLE hWV ((gluedMul hU mulData hmulData i j).app (op V) x y)
      = (mulData i j m).app W hm ((piece i).val.resLE hWV x) ((piece j).val.resLE hWV y) :=
  (resLE_gluedMul_app hU mulData hmulData i j hWV x y).trans
    (gluedMul_app hU mulData hmulData i j m W hm _ _)

/-- The restriction of the glued unit to an open contained in a member of the cover is that
member's own local unit. -/
public theorem resLE_gluedOne_eval_eq (m : ι) {V W : X.Opens} (hWV : W ≤ V) (hm : W ≤ U m) :
    (piece 0).val.resLE hWV ((gluedOne hU oneData honeData).eval (op V))
      = (oneData m).app W hm :=
  (resLE_gluedOne_eval hU oneData honeData hWV).trans
    (gluedOne_eval hU oneData honeData m W hm)

/-- **A sheaf of `ℤ`-graded algebras, glued from local ones over an open cover.**

The homogeneous pieces are given globally; the multiplication and the unit are given only on the
members of an open cover, agree on all overlaps, and satisfy associativity and the two unit laws
there. The glued multiplication and unit then satisfy those laws globally, because each is a
heterogeneous equation between sections of two pieces whose degrees agree propositionally, and
such an equation may be checked on a cover
(`Stacks.AlgebraicGeometry.ModuleBilinearGlue.heq_of_cover`).

Unconditional in `X`, in the cover and in the pieces: only the sheaf condition of the pieces is
used, and it is part of the definition of `AlgebraicGeometry.Scheme.Modules`. The result is at the
type `SheafOfModules.GradedAlgebra X.ringCatSheaf`, which is
`Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra X` by
`Stacks.CategoryTheory.RingedSite.ringSheaf_ofScheme`. -/
public def gluedGradedAlgebra
    (hassoc : ∀ (i j k : ℤ) (m : ι) (V : X.Opens) (hV : V ≤ U m) (x : Γ(piece i, V))
        (y : Γ(piece j, V)) (z : Γ(piece k, V)),
      HEq ((mulData (i + j) k m).app V hV ((mulData i j m).app V hV x y) z)
        ((mulData i (j + k) m).app V hV x ((mulData j k m).app V hV y z)))
    (hone_mul : ∀ (i : ℤ) (m : ι) (V : X.Opens) (hV : V ≤ U m) (x : Γ(piece i, V)),
      HEq ((mulData 0 i m).app V hV ((oneData m).app V hV) x) x)
    (hmul_one : ∀ (i : ℤ) (m : ι) (V : X.Opens) (hV : V ≤ U m) (x : Γ(piece i, V)),
      HEq ((mulData i 0 m).app V hV x ((oneData m).app V hV)) x) :
    SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece n := piece n
  mul i j := gluedMul hU mulData hmulData i j
  one := gluedOne hU oneData honeData
  mul_assoc i j k W x y z := by
    refine heq_of_cover (F := piece) (a := i + j + k) (b := i + (j + k)) (add_assoc i j k)
      (V := W.unop) _ _ hU fun m => ?_
    have hm : W.unop ⊓ U m ≤ U m := inf_le_right
    have h₀ : W.unop ⊓ U m ≤ W.unop := inf_le_left
    have eL : (piece (i + j + k)).val.resLE h₀
          ((gluedMul hU mulData hmulData (i + j) k).app (op W.unop)
            ((gluedMul hU mulData hmulData i j).app (op W.unop) x y) z)
        = (mulData (i + j) k m).app (W.unop ⊓ U m) hm
            ((mulData i j m).app (W.unop ⊓ U m) hm ((piece i).val.resLE h₀ x)
              ((piece j).val.resLE h₀ y))
            ((piece k).val.resLE h₀ z) :=
      (resLE_gluedMul_app_eq hU mulData hmulData (i + j) k m h₀ hm _ z).trans
        (congrArg (fun u => (mulData (i + j) k m).app (W.unop ⊓ U m) hm u
            ((piece k).val.resLE h₀ z))
          (resLE_gluedMul_app_eq hU mulData hmulData i j m h₀ hm x y))
    have eR : (piece (i + (j + k))).val.resLE h₀
          ((gluedMul hU mulData hmulData i (j + k)).app (op W.unop) x
            ((gluedMul hU mulData hmulData j k).app (op W.unop) y z))
        = (mulData i (j + k) m).app (W.unop ⊓ U m) hm ((piece i).val.resLE h₀ x)
            ((mulData j k m).app (W.unop ⊓ U m) hm ((piece j).val.resLE h₀ y)
              ((piece k).val.resLE h₀ z)) :=
      (resLE_gluedMul_app_eq hU mulData hmulData i (j + k) m h₀ hm x _).trans
        (congrArg (fun u => (mulData i (j + k) m).app (W.unop ⊓ U m) hm
            ((piece i).val.resLE h₀ x) u)
          (resLE_gluedMul_app_eq hU mulData hmulData j k m h₀ hm y z))
    exact (heq_of_eq eL).trans
      ((hassoc i j k m (W.unop ⊓ U m) hm _ _ _).trans (heq_of_eq eR.symm))
  one_mul i W x := by
    refine heq_of_cover (F := piece) (a := 0 + i) (b := i) (zero_add i)
      (V := W.unop) _ _ hU fun m => ?_
    have hm : W.unop ⊓ U m ≤ U m := inf_le_right
    have h₀ : W.unop ⊓ U m ≤ W.unop := inf_le_left
    have e : (piece (0 + i)).val.resLE h₀
          ((gluedMul hU mulData hmulData 0 i).app (op W.unop)
            ((gluedOne hU oneData honeData).eval (op W.unop)) x)
        = (mulData 0 i m).app (W.unop ⊓ U m) hm ((oneData m).app (W.unop ⊓ U m) hm)
            ((piece i).val.resLE h₀ x) :=
      (resLE_gluedMul_app_eq hU mulData hmulData 0 i m h₀ hm _ x).trans
        (congrArg (fun u => (mulData 0 i m).app (W.unop ⊓ U m) hm u
            ((piece i).val.resLE h₀ x))
          (resLE_gluedOne_eval_eq hU oneData honeData m h₀ hm))
    exact (heq_of_eq e).trans (hone_mul i m (W.unop ⊓ U m) hm _)
  mul_one i W x := by
    refine heq_of_cover (F := piece) (a := i + 0) (b := i) (add_zero i)
      (V := W.unop) _ _ hU fun m => ?_
    have hm : W.unop ⊓ U m ≤ U m := inf_le_right
    have h₀ : W.unop ⊓ U m ≤ W.unop := inf_le_left
    have e : (piece (i + 0)).val.resLE h₀
          ((gluedMul hU mulData hmulData i 0).app (op W.unop) x
            ((gluedOne hU oneData honeData).eval (op W.unop)))
        = (mulData i 0 m).app (W.unop ⊓ U m) hm ((piece i).val.resLE h₀ x)
            ((oneData m).app (W.unop ⊓ U m) hm) :=
      (resLE_gluedMul_app_eq hU mulData hmulData i 0 m h₀ hm x _).trans
        (congrArg (fun u => (mulData i 0 m).app (W.unop ⊓ U m) hm
            ((piece i).val.resLE h₀ x) u)
          (resLE_gluedOne_eval_eq hU oneData honeData m h₀ hm))
    exact (heq_of_eq e).trans (hmul_one i m (W.unop ⊓ U m) hm _)

end GradedAlgebra

end Stacks.AlgebraicGeometry.ModuleBilinearGlue

end
