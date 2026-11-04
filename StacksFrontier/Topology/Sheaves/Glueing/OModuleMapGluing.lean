module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf

/-!
# Glueing maps of sheaves of `𝒪`-modules over an open covering

Let `X` be a topological space, let `𝒪` be a presheaf of rings on `X`, and let `M` and `N` be
presheaves of `𝒪`-modules with `N` a sheaf. Given an open covering `X = ⋃ i, U i` and maps of
`𝒪`-modules `φ i : M|_{U i} ⟶ N|_{U i}` agreeing on the overlaps, there is a unique map of
`𝒪`-modules `ψ : M ⟶ N` restricting to `φ i` on each `U i`.

This is the morphism half of the sheaf-of-`𝒪`-modules case of Stacks 00AN, and the `𝒪`-module
analogue of Stacks 04TN (`TopCat.Sheaf.existsUnique_hom_of_localHom`).

## Implementation notes

The structure sheaf is *not* constant along the covering: a section of `M` over `V` is a module
over `𝒪(V)`, and restriction to `W ≤ V` is semilinear along `𝒪(V) → 𝒪(W)`. That bookkeeping is
exactly what Mathlib's `PresheafOfModules 𝒪` already encodes, so no new structure is introduced
for it: a presheaf of `𝒪`-modules on `X` is `PresheafOfModules.{u} 𝒪` for
`𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}`, and `(f i).app V hV` below is a morphism of
`ModuleCat (𝒪.obj (op V))`, i.e. an `𝒪(V)`-linear map.

As in `StacksFrontier/Topology/Sheaves/Glueing/MapGluing.lean`, the restriction `M|_{U i}` is not
formed: a map of `𝒪`-modules on an open `U` is recorded directly as a family of `𝒪(V)`-linear maps
`M(V) → N(V)` indexed by the opens `V` of `X` with `V ≤ U`, compatible with restriction
(`TopCat.Sheaf.LocalModuleHom`). Under the order isomorphism between the opens of the subspace `U`
and the opens of `X` contained in `U` this is the same data as a morphism `M|_U ⟶ N|_U`, and it has
the practical advantage that an overlap of two members of the covering is a single open of `X`: in
particular the compatibility hypothesis below is stated over *every* open `V` contained in both
`U i` and `U j`, so the overlaps are never required to belong to the covering family themselves.

Only the sheaf condition for the *target* `N` is used, and only through its underlying presheaf of
sets; `M` is an arbitrary presheaf of `𝒪`-modules.

Two devices keep the proofs short.

* Restriction along an inclusion of opens is used in the bundled semilinear form
  `PresheafOfModules.resLE`, not as `M.map (homOfLE h).op`. The point is the *type*: the codomain
  of `M.map f` is `ModuleCat.restrictScalars (𝒪.map f) (M(W))`, which has the same carrier as
  `M(W)` but is a different expression, so a rewrite under it fails the motive check. The bundled
  form has codomain literally `M(W)`, and being a bundled semilinear map it also makes `map_add`
  and `map_smulₛₗ` apply directly.
* Containment proofs are never transported. Proof irrelevance is definitional in Lean, so
  `M.resLE h s` and `M.resLE h' s` are the same term for any two proofs `h h' : W ≤ V`; the
  normalisation lemma `PresheafOfModules.resLE_resLE` is stated with the composite proof it
  produces, and the residual goals are closed by `rfl`.

The glued morphism is assembled by `PresheafOfModules.homMk` from its underlying map of presheaves
of abelian groups, for the same reason: the naturality square of a morphism of presheaves of
abelian groups has a type not mentioning `ModuleCat.restrictScalars`.

## Main definitions

* `PresheafOfModules.resLE`: restriction along an inclusion of opens, bundled semilinearly.
* `TopCat.Sheaf.LocalModuleHom`: a map of presheaves of `𝒪`-modules on an open `U` of `X`,
  recorded as presheaf-level data on the opens of `X` contained in `U`.
* `TopCat.Sheaf.LocalModuleHom.gluedHom`: the glued morphism of presheaves of `𝒪`-modules.

## Main results

* `TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf`,
  `TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`: the two halves of the sheaf axiom for a
  sheaf of `𝒪`-modules, in terms of its own restriction maps.
* `TopCat.Sheaf.existsUnique_hom_of_localModuleHom`: **the morphism half of the `𝒪`-module case of
  Stacks 00AN.** Maps of sheaves of `𝒪`-modules glue over an open covering.
* `TopCat.Sheaf.eq_hom_of_restrict`: the uniqueness half on its own, with no compatibility or
  glueing hypothesis: a map of `𝒪`-modules into a sheaf is determined by its restrictions to a
  covering.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- Restriction of sections of a presheaf of `𝒪`-modules along an inclusion `W ≤ V` of opens,
bundled as a map semilinear along the ring map `𝒪(V) → 𝒪(W)`, with codomain `M(W)`. -/
noncomputable def resLE (M : PresheafOfModules.{u} 𝒪) {V W : Opens X} (h : W ≤ V) :
    M.obj (op V) →ₛₗ[(𝒪.map (homOfLE h).op).hom] M.obj (op W) :=
  M.restrictₛₗ (homOfLE h).op

/-- `M.resLE h` sends a section `s` over `V` to its restriction `M.map (homOfLE h).op s`. -/
@[simp]
theorem resLE_apply (M : PresheafOfModules.{u} 𝒪) {V W : Opens X} (h : W ≤ V)
    (s : M.obj (op V)) : M.resLE h s = M.map (homOfLE h).op s :=
  rfl

/-- Restricting twice is restricting once. The containment proof on the right is the composite
one; any other proof of the same containment gives the same term, by proof irrelevance. -/
theorem resLE_resLE (M : PresheafOfModules.{u} 𝒪) {V W Z : Opens X} (hWV : W ≤ V) (hZW : Z ≤ W)
    (s : M.obj (op V)) :
    M.resLE hZW (M.resLE hWV s) = M.resLE (hZW.trans hWV) s := by
  rw [resLE_apply, resLE_apply, resLE_apply, ← M.map_comp_apply]
  exact M.congr_map_apply (Subsingleton.elim _ _) s

/-- A morphism of presheaves of `𝒪`-modules commutes with restriction along inclusions of
opens. -/
theorem app_resLE {M N : PresheafOfModules.{u} 𝒪} (ψ : M ⟶ N) {V W : Opens X} (h : W ≤ V)
    (s : M.obj (op V)) : ψ.app (op W) (M.resLE h s) = N.resLE h (ψ.app (op V) s) :=
  naturality_apply ψ (homOfLE h).op s

end PresheafOfModules

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-! ### The sheaf axiom for a sheaf of `𝒪`-modules -/

/-- The underlying presheaf of sets of a sheaf of `𝒪`-modules, viewed as a
`TopCat.Sheaf.LocalPresheaf` on the whole space, satisfies the sheaf condition. -/
theorem isSheaf_toLocalPresheaf_presheaf {N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf) :
    (TopCat.Presheaf.toLocalPresheaf
      (N.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) (⊤ : Opens X)).IsSheaf :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    (CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _
      (CategoryTheory.forget AddCommGrpCat.{u}) hN) ⊤

/-- The glueing half of the sheaf axiom for a sheaf of `𝒪`-modules, stated with the restriction
maps of the presheaf of modules itself: a compatible family of sections over a covering of an open
`V` by opens of `X` comes from a unique section over `V`. -/
theorem existsUnique_gluing_of_isSheafPresheaf {N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    {ι : Type u} {V : Opens X} (W : ι → Opens X) (hWV : ∀ k, W k ≤ V) (hcov : V ≤ ⨆ k, W k)
    (s : ∀ k, N.obj (op (W k)))
    (hs : ∀ k l, N.resLE (inf_le_left : W k ⊓ W l ≤ W k) (s k)
      = N.resLE (inf_le_right : W k ⊓ W l ≤ W l) (s l)) :
    ∃! t : N.obj (op V), ∀ k, N.resLE (hWV k) t = s k :=
  isSheaf_toLocalPresheaf_presheaf hN le_top W hWV hcov s hs

/-- The separation half of the sheaf axiom for a sheaf of `𝒪`-modules: a section is determined by
its restrictions to a covering. -/
theorem eq_of_locally_eq_of_isSheafPresheaf {N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    {ι : Type u} {V : Opens X} (W : ι → Opens X) (hWV : ∀ k, W k ≤ V) (hcov : V ≤ ⨆ k, W k)
    {a b : N.obj (op V)} (h : ∀ k, N.resLE (hWV k) a = N.resLE (hWV k) b) : a = b :=
  (isSheaf_toLocalPresheaf_presheaf hN).eq_of_locally_eq (hV := le_top) W hWV hcov h

/-! ### Local maps of presheaves of `𝒪`-modules -/

/-- A *local map of presheaves of `𝒪`-modules* `M → N` on an open subset `U` of `X`: a family of
`𝒪(V)`-linear maps `M(V) → N(V)`, one for each open `V` of `X` contained in `U`, compatible with
all restriction maps.

This is the same data as a morphism of presheaves of `𝒪|_U`-modules `M|_U ⟶ N|_U`, via the
canonical order isomorphism between the opens of the subspace `U` and the opens of `X` contained
in `U`; recording it this way means an overlap of two opens is a single open of `X`, so no
transport is ever needed. Compare `TopCat.Sheaf.LocalSheafHom` for sheaves of sets. -/
structure LocalModuleHom (M N : PresheafOfModules.{u} 𝒪) (U : Opens X) where
  /-- The `𝒪(V)`-linear map on sections over an open `V ≤ U`. -/
  app : ∀ (V : Opens X), V ≤ U → (M.obj (op V) ⟶ N.obj (op V))
  /-- Compatibility with the restriction maps of `M` and `N`. -/
  naturality : ∀ {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V) (s : M.obj (op V)),
    app W (hWV.trans hV) (M.resLE hWV s) = N.resLE hWV (app V hV s)

/-- Every open `V` is covered by the opens `V ⊓ U i`, since the `U i` cover `X`. -/
theorem le_iSup_inf {ι : Type u} {U : ι → Opens X} (hU : ⨆ i, U i = ⊤) (V : Opens X) :
    V ≤ ⨆ i, V ⊓ U i := by
  have h : V ⊓ ⨆ i, U i = ⨆ i, V ⊓ U i := inf_iSup_eq V U
  rw [hU, inf_top_eq] at h
  exact h.le

namespace LocalModuleHom

variable {M N : PresheafOfModules.{u} 𝒪} {ι : Type u} {U : ι → Opens X}

/-- The local value of the glued map on a section `s` over `V`: the image under `φ i` of the
restriction of `s` to `V ⊓ U i`. -/
noncomputable def localValue (f : ∀ i, LocalModuleHom M N (U i)) {V : Opens X}
    (s : M.obj (op V)) (i : ι) :
    N.obj (op (V ⊓ U i)) :=
  (f i).app (V ⊓ U i) inf_le_right (M.resLE (inf_le_left : V ⊓ U i ≤ V) s)

/-- The local values of a section are compatible on the overlaps: on an open contained in both
`V ⊓ U i` and `V ⊓ U j` both are computed from `s` by a single restriction followed by the common
value of `φ i` and `φ j` there. -/
theorem resLE_localValue_eq (f : ∀ i, LocalModuleHom M N (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj)
    {V : Opens X} (s : M.obj (op V)) (i j : ι) {Z : Opens X} (hi : Z ≤ V ⊓ U i)
    (hj : Z ≤ V ⊓ U j) :
    N.resLE hi (localValue f s i) = N.resLE hj (localValue f s j) := by
  rw [localValue, localValue, ← (f i).naturality inf_le_right hi,
    ← (f j).naturality inf_le_right hj, M.resLE_resLE, M.resLE_resLE,
    hf i j Z (hi.trans inf_le_right) (hj.trans inf_le_right)]

variable (hU : ⨆ i, U i = ⊤)
  (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
  (f : ∀ i, LocalModuleHom M N (U i))
  (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
    (f i).app V hVi = (f j).app V hVj)

/-- The glued section over `V`: the unique section of `N` over `V` whose restriction to each
`V ⊓ U i` is `localValue f s i`. -/
noncomputable def gluedValue (V : Opens X) (s : M.obj (op V)) : N.obj (op V) :=
  (existsUnique_gluing_of_isSheafPresheaf hN (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) (localValue f s)
    (fun k l => resLE_localValue_eq f hf s k l inf_le_left inf_le_right)).choose

/-- The defining property of `gluedValue`: it restricts to the local values. -/
theorem resLE_gluedValue (V : Opens X) (s : M.obj (op V)) (i : ι) :
    N.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValue hU hN f hf V s) = localValue f s i := by
  unfold gluedValue
  generalize_proofs _ _ h
  exact h.choose_spec.1 i

/-- `gluedValue` is characterised by its defining property. -/
theorem eq_gluedValue {V : Opens X} {s : M.obj (op V)} (y : N.obj (op V))
    (hy : ∀ i, N.resLE (inf_le_left : V ⊓ U i ≤ V) y = localValue f s i) :
    y = gluedValue hU hN f hf V s :=
  eq_of_locally_eq_of_isSheafPresheaf hN (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU V) fun i => (hy i).trans (resLE_gluedValue hU hN f hf V s i).symm

/-- The glued section map is additive. -/
theorem gluedValue_add {V : Opens X} (s t : M.obj (op V)) :
    gluedValue hU hN f hf V (s + t)
      = gluedValue hU hN f hf V s + gluedValue hU hN f hf V t :=
  (eq_gluedValue hU hN f hf _ fun i => by
    rw [map_add, resLE_gluedValue hU hN f hf V s i, resLE_gluedValue hU hN f hf V t i,
      localValue, localValue, localValue, map_add, map_add]).symm

/-- The glued section map is `𝒪(V)`-linear. -/
theorem gluedValue_smul {V : Opens X} (r : 𝒪.obj (op V)) (s : M.obj (op V)) :
    gluedValue hU hN f hf V (r • s) = r • gluedValue hU hN f hf V s :=
  (eq_gluedValue hU hN f hf _ fun i => by
    rw [map_smulₛₗ, resLE_gluedValue hU hN f hf V s i, localValue, localValue, map_smulₛₗ,
      map_smul]).symm

/-- The glued section map commutes with the restriction maps. -/
theorem gluedValue_resLE {V W : Opens X} (hWV : W ≤ V) (s : M.obj (op V)) :
    gluedValue hU hN f hf W (M.resLE hWV s)
      = N.resLE hWV (gluedValue hU hN f hf V s) := by
  refine (eq_gluedValue hU hN f hf _ fun i => ?_).symm
  have hk : W ⊓ U i ≤ V ⊓ U i := inf_le_inf_right (U i) hWV
  have h1 : N.resLE (inf_le_left : W ⊓ U i ≤ W) (N.resLE hWV (gluedValue hU hN f hf V s))
      = N.resLE hk (N.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValue hU hN f hf V s)) := by
    rw [N.resLE_resLE, N.resLE_resLE]
  rw [h1, resLE_gluedValue hU hN f hf V s i, localValue, localValue,
    ← (f i).naturality inf_le_right hk, M.resLE_resLE, M.resLE_resLE]

/-- On an open contained in a member of the covering, the glued section map is the corresponding
local map. -/
theorem gluedValue_eq_app {i : ι} {V : Opens X} (hV : V ≤ U i) (s : M.obj (op V)) :
    gluedValue hU hN f hf V s = (f i).app V hV s :=
  (eq_gluedValue hU hN f hf _ fun j => by
    rw [← (f i).naturality hV (inf_le_left : V ⊓ U j ≤ V), localValue,
      hf i j (V ⊓ U j) (inf_le_left.trans hV) inf_le_right]).symm

/-- The map of presheaves of abelian groups underlying the glued morphism of presheaves of
`𝒪`-modules. -/
noncomputable def gluedAddHom : M.presheaf ⟶ N.presheaf where
  app Y := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (gluedValue hU hN f hf Y.unop) (gluedValue_add hU hN f hf))
  naturality Y Z g := by
    ext s
    rw [show g = (homOfLE (Quiver.Hom.unop g).le).op from Subsingleton.elim _ _]
    exact gluedValue_resLE hU hN f hf (Quiver.Hom.unop g).le s

/-- **The glued morphism of presheaves of `𝒪`-modules.** -/
noncomputable def gluedHom : M ⟶ N :=
  PresheafOfModules.homMk (gluedAddHom hU hN f hf) fun _ => gluedValue_smul hU hN f hf

/-- The glued morphism restricts to `φ i` over every open contained in `U i`. -/
theorem gluedHom_app (i : ι) (V : Opens X) (hV : V ≤ U i) :
    (gluedHom hU hN f hf).app (op V) = (f i).app V hV :=
  ModuleCat.hom_ext (LinearMap.ext fun s => gluedValue_eq_app hU hN f hf hV s)

end LocalModuleHom

/-- The uniqueness half, on its own: a map of presheaves of `𝒪`-modules into a sheaf is determined
by its restrictions to a covering. No compatibility hypothesis on the local maps is needed, and
they enter only through the equations the two morphisms are asserted to satisfy. -/
theorem eq_hom_of_restrict {ι : Type u} {U : ι → Opens X} (hU : ⨆ i, U i = ⊤)
    {M N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    (g : ∀ (i : ι) (V : Opens X), V ≤ U i → (M.obj (op V) ⟶ N.obj (op V))) {ψ ψ' : M ⟶ N}
    (hψ : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), ψ.app (op V) = g i V hV)
    (hψ' : ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), ψ'.app (op V) = g i V hV) :
    ψ = ψ' := by
  refine PresheafOfModules.hom_ext fun Y => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  refine eq_of_locally_eq_of_isSheafPresheaf hN (fun i => Y.unop ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf hU Y.unop) fun i => ?_
  rw [← PresheafOfModules.app_resLE ψ (inf_le_left : Y.unop ⊓ U i ≤ Y.unop) s,
    ← PresheafOfModules.app_resLE ψ' (inf_le_left : Y.unop ⊓ U i ≤ Y.unop) s,
    hψ i (Y.unop ⊓ U i) inf_le_right, hψ' i (Y.unop ⊓ U i) inf_le_right]

/-- **The morphism half of the sheaf-of-`𝒪`-modules case of Stacks 00AN**, the `𝒪`-module analogue
of Stacks 04TN. Let `𝒪` be a presheaf of rings on a topological space `X`, let `U : ι → Opens X`
be an open covering of `X`, let `M` be a presheaf of `𝒪`-modules and let `N` be a sheaf of
`𝒪`-modules. Local maps of `𝒪`-modules `φ i : M|_{U i} ⟶ N|_{U i}` agreeing on all overlaps glue
to a unique morphism of presheaves of `𝒪`-modules `ψ : M ⟶ N` restricting to `φ i` on each
`U i`.

The compatibility hypothesis is stated over every open `V` contained in both `U i` and `U j`, so
the overlaps are not required to belong to the covering family. -/
theorem existsUnique_hom_of_localModuleHom {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (M N : PresheafOfModules.{u} 𝒪)
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    (f : ∀ i, LocalModuleHom M N (U i))
    (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
      (f i).app V hVi = (f j).app V hVj) :
    ∃! ψ : M ⟶ N, ∀ (i : ι) (V : Opens X) (hV : V ≤ U i), ψ.app (op V) = (f i).app V hV :=
  ⟨LocalModuleHom.gluedHom hU hN f hf, LocalModuleHom.gluedHom_app hU hN f hf,
    fun _ hψ => eq_hom_of_restrict hU hN (fun i V hV => (f i).app V hV) hψ
      (LocalModuleHom.gluedHom_app hU hN f hf)⟩

end TopCat.Sheaf
