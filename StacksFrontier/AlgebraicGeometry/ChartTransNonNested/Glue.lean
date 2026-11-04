module

public import StacksFrontier.AlgebraicGeometry.SchemeModuleGlue.Chart

/-!
# Glueing maps and isomorphisms of sheaves of `𝒪`-modules over a sub-open

Let `𝒪` be a presheaf of rings on a topological space `X` and `U : ι → Opens X` a family of opens.
Local maps of sheaves of `𝒪`-modules on the members of the family, agreeing on all overlaps, glue
to a local map on any open `W ≤ ⨆ i, U i`; likewise local isomorphisms glue to a local
isomorphism. The open `W` need not be the whole space.

## Main definitions

* `TopCat.Sheaf.LocalModuleHom.glueLE`: **the glued local map over a sub-open.** Local maps on
  the members of a family, agreeing on all overlaps, glue to a local map on any open contained in
  the supremum of the family.
* `TopCat.Sheaf.LocalModuleEquiv`: a local *isomorphism* of presheaves of `𝒪`-modules on an open
  — the same data as `TopCat.Sheaf.LocalModuleHom` with each component a linear equivalence.
* `TopCat.Sheaf.LocalModuleEquiv.glueLE`: **the glued local isomorphism over a sub-open.**

## Main results

* `TopCat.Sheaf.LocalModuleHom.glueLE_app_of_le`: over an open contained in a member of the
  family, the glued map is that member's map.
* `TopCat.Sheaf.LocalModuleHom.eq_of_eq_on_cover`: two local maps on an open agreeing over every
  member of a covering family of that open are equal.
* `TopCat.Sheaf.LocalModuleEquiv.glueLE_app_of_le` and
  `TopCat.Sheaf.LocalModuleEquiv.glueLE_symm_app_of_le`: both directions of the glued isomorphism
  over an open contained in a member.

## Implementation notes

Containment proofs are never transported: proof irrelevance is definitional, so a statement about
`glueLE` at one proof of `V ≤ W` is a statement about it at every other, and the lemmas below
take the two containments they need as separate arguments rather than deriving one from the
other.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- **An open contained in the supremum of a family is covered by its meets with the members.**
The relative form of `TopCat.Sheaf.le_iSup_inf`, which assumes the family covers the space. -/
public theorem le_iSup_inf_of_le {ι : Type u} {U : ι → Opens X} {V : Opens X}
    (hV : V ≤ ⨆ i, U i) : V ≤ ⨆ i, V ⊓ U i := by
  have h : V ⊓ ⨆ i, U i = ⨆ i, V ⊓ U i := inf_iSup_eq V U
  rw [inf_eq_left.mpr hV] at h
  exact h.le

namespace LocalModuleHom

variable {M N : PresheafOfModules.{u} 𝒪} {ι : Type u} {U : ι → Opens X}

section Glue

variable (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
  (f : ∀ i, LocalModuleHom M N (U i))
  (hf : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j),
    (f i).app V hVi = (f j).app V hVj)

/-- The glued section over an open `V` contained in the supremum of the family: the unique section
of `N` over `V` restricting to `TopCat.Sheaf.LocalModuleHom.localValue` on each `V ⊓ U i`. -/
public noncomputable def gluedValueLE {V : Opens X} (hV : V ≤ ⨆ i, U i) (s : M.obj (op V)) :
    N.obj (op V) :=
  (existsUnique_gluing_of_isSheafPresheaf hN (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf_of_le hV) (localValue f s)
    (fun k l => resLE_localValue_eq f hf s k l inf_le_left inf_le_right)).choose

/-- The defining property of `TopCat.Sheaf.LocalModuleHom.gluedValueLE`. -/
public theorem resLE_gluedValueLE {V : Opens X} (hV : V ≤ ⨆ i, U i) (s : M.obj (op V)) (i : ι) :
    N.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValueLE hN f hf hV s) = localValue f s i :=
  (existsUnique_gluing_of_isSheafPresheaf hN (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf_of_le hV) (localValue f s)
    (fun k l => resLE_localValue_eq f hf s k l inf_le_left inf_le_right)).choose_spec.1 i

/-- `TopCat.Sheaf.LocalModuleHom.gluedValueLE` is characterised by its defining property. -/
public theorem eq_gluedValueLE {V : Opens X} (hV : V ≤ ⨆ i, U i) {s : M.obj (op V)}
    (y : N.obj (op V))
    (hy : ∀ i, N.resLE (inf_le_left : V ⊓ U i ≤ V) y = localValue f s i) :
    y = gluedValueLE hN f hf hV s :=
  eq_of_locally_eq_of_isSheafPresheaf hN (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (le_iSup_inf_of_le hV) fun i => (hy i).trans (resLE_gluedValueLE hN f hf hV s i).symm

/-- The glued section map is additive. -/
public theorem gluedValueLE_add {V : Opens X} (hV : V ≤ ⨆ i, U i) (s t : M.obj (op V)) :
    gluedValueLE hN f hf hV (s + t)
      = gluedValueLE hN f hf hV s + gluedValueLE hN f hf hV t :=
  (eq_gluedValueLE hN f hf hV _ fun i => by
    rw [map_add, resLE_gluedValueLE hN f hf hV s i, resLE_gluedValueLE hN f hf hV t i,
      localValue, localValue, localValue, map_add, map_add]).symm

/-- The glued section map is `𝒪(V)`-linear. -/
public theorem gluedValueLE_smul {V : Opens X} (hV : V ≤ ⨆ i, U i) (r : 𝒪.obj (op V))
    (s : M.obj (op V)) :
    gluedValueLE hN f hf hV (r • s) = r • gluedValueLE hN f hf hV s :=
  (eq_gluedValueLE hN f hf hV _ fun i => by
    rw [map_smulₛₗ, resLE_gluedValueLE hN f hf hV s i, localValue, localValue, map_smulₛₗ,
      map_smul]).symm

/-- The glued section map commutes with the restriction maps. -/
public theorem gluedValueLE_resLE {V W : Opens X} (hV : V ≤ ⨆ i, U i) (hW : W ≤ ⨆ i, U i)
    (hWV : W ≤ V) (s : M.obj (op V)) :
    gluedValueLE hN f hf hW (M.resLE hWV s) = N.resLE hWV (gluedValueLE hN f hf hV s) := by
  refine (eq_gluedValueLE hN f hf hW _ fun i => ?_).symm
  have hk : W ⊓ U i ≤ V ⊓ U i := inf_le_inf_right (U i) hWV
  have h1 : N.resLE (inf_le_left : W ⊓ U i ≤ W) (N.resLE hWV (gluedValueLE hN f hf hV s))
      = N.resLE hk (N.resLE (inf_le_left : V ⊓ U i ≤ V) (gluedValueLE hN f hf hV s)) := by
    rw [N.resLE_resLE, N.resLE_resLE]
  rw [h1, resLE_gluedValueLE hN f hf hV s i, localValue, localValue,
    ← (f i).naturality inf_le_right hk, M.resLE_resLE, M.resLE_resLE]

/-- Over an open contained in a member of the family, the glued section map is that member's
map. -/
public theorem gluedValueLE_eq_app {i : ι} {V : Opens X} (hV : V ≤ ⨆ i, U i) (hVi : V ≤ U i)
    (s : M.obj (op V)) : gluedValueLE hN f hf hV s = (f i).app V hVi s :=
  (eq_gluedValueLE hN f hf hV _ fun j => by
    rw [← (f i).naturality hVi (inf_le_left : V ⊓ U j ≤ V), localValue,
      hf i j (V ⊓ U j) (inf_le_left.trans hVi) inf_le_right]).symm

/-- The `𝒪(V)`-linear map glued over an open `V` contained in the supremum of the family. -/
public noncomputable def gluedLinearMap {V : Opens X} (hV : V ≤ ⨆ i, U i) :
    M.obj (op V) ⟶ N.obj (op V) :=
  ModuleCat.ofHom
    { toFun := gluedValueLE hN f hf hV
      map_add' := gluedValueLE_add hN f hf hV
      map_smul' := gluedValueLE_smul hN f hf hV }

/-- The glued linear map sends a section to its glued value. -/
@[simp]
public theorem gluedLinearMap_apply {V : Opens X} (hV : V ≤ ⨆ i, U i) (s : M.obj (op V)) :
    gluedLinearMap hN f hf hV s = gluedValueLE hN f hf hV s :=
  rfl

/-- **The glued local map over a sub-open.** Local maps of `𝒪`-modules on the members of a family,
agreeing on all overlaps, glue to a local map on any open contained in the supremum of the
family. -/
public noncomputable def glueLE {W : Opens X} (hW : W ≤ ⨆ i, U i) : LocalModuleHom M N W where
  app _ hV := gluedLinearMap hN f hf (hV.trans hW)
  naturality hV hWV s := gluedValueLE_resLE hN f hf (hV.trans hW) ((hWV.trans hV).trans hW) hWV s

/-- Over an open contained in a member of the family, the glued local map is that member's map. -/
public theorem glueLE_app_of_le {W : Opens X} (hW : W ≤ ⨆ i, U i) {i : ι} {V : Opens X}
    (hVW : V ≤ W) (hVi : V ≤ U i) (s : M.obj (op V)) :
    (glueLE hN f hf hW).app V hVW s = (f i).app V hVi s :=
  gluedValueLE_eq_app hN f hf (hVW.trans hW) hVi s

end Glue

/-! ### The separation half for local maps -/

/-- Into a sheaf, two local maps on an open `W` that agree over every open contained in both `W`
and a member of a family covering `W` are equal. -/
public theorem eq_of_eq_on_cover
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    {κ : Type u} {L : κ → Opens X} {W : Opens X} (hW : W ≤ ⨆ k, L k)
    {g g' : LocalModuleHom M N W}
    (h : ∀ (k : κ) (V : Opens X) (hVW : V ≤ W) (_hVk : V ≤ L k) (s : M.obj (op V)),
      g.app V hVW s = g'.app V hVW s)
    (V : Opens X) (hV : V ≤ W) (s : M.obj (op V)) : g.app V hV s = g'.app V hV s := by
  refine eq_of_locally_eq_of_isSheafPresheaf hN (fun k => V ⊓ L k) (fun _ => inf_le_left)
    (le_iSup_inf_of_le (hV.trans hW)) fun k => ?_
  rw [← g.naturality hV (inf_le_left : V ⊓ L k ≤ V), ← g'.naturality hV inf_le_left,
    h k (V ⊓ L k) (inf_le_left.trans hV) inf_le_right]

/-! ### Identities and composites of local maps -/

/-- The identity local map on an open. -/
public noncomputable def idLocal (M : PresheafOfModules.{u} 𝒪) (W : Opens X) :
    LocalModuleHom M M W where
  app _ _ := 𝟙 _
  naturality _ _ s := by rw [ConcreteCategory.id_apply, ConcreteCategory.id_apply]

/-- Each component of the identity local map is the identity on sections. -/
@[simp]
public theorem idLocal_app (M : PresheafOfModules.{u} 𝒪) (W V : Opens X) (hV : V ≤ W)
    (s : M.obj (op V)) : (idLocal M W).app V hV s = s :=
  ConcreteCategory.id_apply _

/-- The composite of two local maps on the same open. -/
public noncomputable def compLocal {P : PresheafOfModules.{u} 𝒪} {W : Opens X}
    (g : LocalModuleHom M N W) (g' : LocalModuleHom N P W) : LocalModuleHom M P W where
  app V hV := g.app V hV ≫ g'.app V hV
  naturality hV hWV s := by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, g.naturality hV hWV,
      g'.naturality hV hWV]

/-- Each component of a composite of local maps is the composite of the components. -/
@[simp]
public theorem compLocal_app {P : PresheafOfModules.{u} 𝒪} {W : Opens X}
    (g : LocalModuleHom M N W) (g' : LocalModuleHom N P W) (V : Opens X) (hV : V ≤ W)
    (s : M.obj (op V)) : (compLocal g g').app V hV s = g'.app V hV (g.app V hV s) :=
  ConcreteCategory.comp_apply _ _ _

/-- Into a sheaf, a pair of local maps on `W` whose composite is the identity over every open in
a member of a family covering `W` composes to the identity on all sections over opens in `W`. -/
private theorem app_app_eq_self_of_eq_on_cover
    (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
    {κ : Type u} {L : κ → Opens X} {W : Opens X} (hW : W ≤ ⨆ k, L k)
    (g : LocalModuleHom M N W) (g' : LocalModuleHom N M W)
    (h : ∀ (k : κ) (V : Opens X) (hVW : V ≤ W) (_hVk : V ≤ L k) (s : M.obj (op V)),
      g'.app V hVW (g.app V hVW s) = s)
    (V : Opens X) (hV : V ≤ W) (s : M.obj (op V)) : g'.app V hV (g.app V hV s) = s := by
  simpa using eq_of_eq_on_cover hM hW (g := compLocal g g') (g' := idLocal M W)
    (fun k V hVW hVk s => by simpa using h k V hVW hVk s) V hV s

end LocalModuleHom

/-! ### Local isomorphisms -/

/-- **A local isomorphism of presheaves of `𝒪`-modules on an open `U` of `X`:** a family of
`𝒪(V)`-linear equivalences `M(V) ≃ N(V)`, one for each open `V` of `X` contained in `U`,
compatible with all restriction maps.

This is `TopCat.Sheaf.LocalModuleHom` with each component invertible. Only the naturality of the
forward direction is recorded; that of the inverse follows
(`TopCat.Sheaf.LocalModuleEquiv.symm_naturality`). -/
public structure LocalModuleEquiv (M N : PresheafOfModules.{u} 𝒪) (U : Opens X) where
  /-- The `𝒪(V)`-linear equivalence on sections over an open `V ≤ U`. -/
  app : ∀ (V : Opens X), V ≤ U → (M.obj (op V) ≃ₗ[𝒪.obj (op V)] N.obj (op V))
  /-- Compatibility with the restriction maps of `M` and `N`. -/
  naturality : ∀ {V W : Opens X} (hV : V ≤ U) (hWV : W ≤ V) (s : M.obj (op V)),
    app W (hWV.trans hV) (M.resLE hWV s) = N.resLE hWV (app V hV s)

namespace LocalModuleEquiv

variable {M N : PresheafOfModules.{u} 𝒪} {ι : Type u} {U : ι → Opens X}

/-- The inverse of a local isomorphism also commutes with the restriction maps. -/
public theorem symm_naturality {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) {V W : Opens X}
    (hV : V ≤ W₀) (hWV : W ≤ V) (t : N.obj (op V)) :
    (e.app W (hWV.trans hV)).symm (N.resLE hWV t) = M.resLE hWV ((e.app V hV).symm t) := by
  refine (e.app W (hWV.trans hV)).injective ?_
  rw [LinearEquiv.apply_symm_apply, e.naturality hV hWV, LinearEquiv.apply_symm_apply]

/-- The underlying local map of a local isomorphism. -/
public noncomputable def toLocalModuleHom {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) :
    LocalModuleHom M N W₀ where
  app V hV := ModuleCat.ofHom (e.app V hV).toLinearMap
  naturality hV hWV s := e.naturality hV hWV s

/-- Each component of the underlying local map of a local isomorphism is the corresponding
linear equivalence. -/
@[simp]
public theorem toLocalModuleHom_app {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) (V : Opens X)
    (hV : V ≤ W₀) (s : M.obj (op V)) : e.toLocalModuleHom.app V hV s = e.app V hV s :=
  rfl

/-- The inverse local map of a local isomorphism. -/
public noncomputable def symmLocalModuleHom {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) :
    LocalModuleHom N M W₀ where
  app V hV := ModuleCat.ofHom (e.app V hV).symm.toLinearMap
  naturality hV hWV t := e.symm_naturality hV hWV t

/-- Each component of the inverse local map of a local isomorphism is the inverse of the
corresponding linear equivalence. -/
@[simp]
public theorem symmLocalModuleHom_app {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) (V : Opens X)
    (hV : V ≤ W₀) (t : N.obj (op V)) :
    e.symmLocalModuleHom.app V hV t = (e.app V hV).symm t :=
  rfl

/-- The inverse of a local isomorphism. -/
public noncomputable def symm {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) :
    LocalModuleEquiv N M W₀ where
  app V hV := (e.app V hV).symm
  naturality hV hWV t := e.symm_naturality hV hWV t

/-- Each component of the inverse of a local isomorphism is the inverse of the corresponding
linear equivalence. -/
@[simp]
public theorem symm_app {W₀ : Opens X} (e : LocalModuleEquiv M N W₀) (V : Opens X) (hV : V ≤ W₀)
    (t : N.obj (op V)) : e.symm.app V hV t = (e.app V hV).symm t :=
  rfl

/-- The composite of two local isomorphisms on the same open. -/
public noncomputable def trans {P : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (e : LocalModuleEquiv M N W₀) (e' : LocalModuleEquiv N P W₀) : LocalModuleEquiv M P W₀ where
  app V hV := (e.app V hV).trans (e'.app V hV)
  naturality hV hWV s :=
    (congrArg (e'.app _ (hWV.trans hV)) (e.naturality hV hWV s)).trans
      (e'.naturality hV hWV (e.app _ hV s))

/-- Each component of a composite of local isomorphisms is the composite of the components. -/
@[simp]
public theorem trans_app {P : PresheafOfModules.{u} 𝒪} {W₀ : Opens X}
    (e : LocalModuleEquiv M N W₀) (e' : LocalModuleEquiv N P W₀) (V : Opens X) (hV : V ≤ W₀)
    (s : M.obj (op V)) : (e.trans e').app V hV s = e'.app V hV (e.app V hV s) :=
  rfl

/-- The inverses of a family of local isomorphisms agreeing on the overlaps agree there too. -/
public theorem symm_app_eq (e : ∀ i, LocalModuleEquiv M N (U i))
    (he : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j) (s : M.obj (op V)),
      (e i).app V hVi s = (e j).app V hVj s)
    (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j) (t : N.obj (op V)) :
    ((e i).app V hVi).symm t = ((e j).app V hVj).symm t :=
  ((e i).app V hVi).injective <|
    (LinearEquiv.apply_symm_apply ((e i).app V hVi) t).trans
      ((he i j V hVi hVj _).trans (LinearEquiv.apply_symm_apply ((e j).app V hVj) t)).symm

section Glue

variable (hM : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) M.presheaf)
  (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
  (e : ∀ i, LocalModuleEquiv M N (U i))
  (he : ∀ (i j : ι) (V : Opens X) (hVi : V ≤ U i) (hVj : V ≤ U j) (s : M.obj (op V)),
    (e i).app V hVi s = (e j).app V hVj s)

/-- The forward direction of the glued isomorphism, as a local map. -/
public noncomputable def gluedHom {W : Opens X} (hW : W ≤ ⨆ i, U i) : LocalModuleHom M N W :=
  LocalModuleHom.glueLE hN (fun i => (e i).toLocalModuleHom)
    (fun i j V hVi hVj => ModuleCat.hom_ext (LinearMap.ext (he i j V hVi hVj))) hW

/-- The inverse direction of the glued isomorphism, as a local map. -/
public noncomputable def gluedSymmHom {W : Opens X} (hW : W ≤ ⨆ i, U i) :
    LocalModuleHom N M W :=
  LocalModuleHom.glueLE hM (fun i => (e i).symmLocalModuleHom)
    (fun i j V hVi hVj => ModuleCat.hom_ext (LinearMap.ext (symm_app_eq e he i j V hVi hVj))) hW

/-- Over an open contained in a member of the family, the forward direction of the glued
isomorphism is that member's. -/
public theorem gluedHom_app_of_le {W : Opens X} (hW : W ≤ ⨆ i, U i) {i : ι} {V : Opens X}
    (hVW : V ≤ W) (hVi : V ≤ U i) (s : M.obj (op V)) :
    (gluedHom hN e he hW).app V hVW s = (e i).app V hVi s :=
  LocalModuleHom.glueLE_app_of_le _ _ _ hW hVW hVi s

/-- Over an open contained in a member of the family, the inverse direction of the glued
isomorphism is that member's. -/
public theorem gluedSymmHom_app_of_le {W : Opens X} (hW : W ≤ ⨆ i, U i) {i : ι} {V : Opens X}
    (hVW : V ≤ W) (hVi : V ≤ U i) (t : N.obj (op V)) :
    (gluedSymmHom hM e he hW).app V hVW t = ((e i).app V hVi).symm t :=
  LocalModuleHom.glueLE_app_of_le _ _ _ hW hVW hVi t

/-- The two glued directions are mutually inverse: the inverse after the forward direction is the
identity. -/
public theorem gluedSymmHom_gluedHom {W : Opens X} (hW : W ≤ ⨆ i, U i) (V : Opens X)
    (hV : V ≤ W) (s : M.obj (op V)) :
    (gluedSymmHom hM e he hW).app V hV ((gluedHom hN e he hW).app V hV s) = s :=
  LocalModuleHom.app_app_eq_self_of_eq_on_cover hM hW (gluedHom hN e he hW)
    (gluedSymmHom hM e he hW)
    (fun i V hVW hVi s => by
      rw [gluedHom_app_of_le hN e he hW hVW hVi, gluedSymmHom_app_of_le hM e he hW hVW hVi,
        LinearEquiv.symm_apply_apply]) V hV s

/-- The two glued directions are mutually inverse: the forward direction after the inverse is the
identity. -/
public theorem gluedHom_gluedSymmHom {W : Opens X} (hW : W ≤ ⨆ i, U i) (V : Opens X)
    (hV : V ≤ W) (t : N.obj (op V)) :
    (gluedHom hN e he hW).app V hV ((gluedSymmHom hM e he hW).app V hV t) = t :=
  LocalModuleHom.app_app_eq_self_of_eq_on_cover hN hW (gluedSymmHom hM e he hW)
    (gluedHom hN e he hW)
    (fun i V hVW hVi t => by
      rw [gluedSymmHom_app_of_le hM e he hW hVW hVi, gluedHom_app_of_le hN e he hW hVW hVi,
        LinearEquiv.apply_symm_apply]) V hV t

/-- **The glued local isomorphism over a sub-open.** Local isomorphisms of `𝒪`-modules on the
members of a family, agreeing on all overlaps, glue to a local isomorphism on any open contained
in the supremum of the family. -/
public noncomputable def glueLE {W : Opens X} (hW : W ≤ ⨆ i, U i) : LocalModuleEquiv M N W where
  app V hV :=
    { toFun := (gluedHom hN e he hW).app V hV
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := (gluedSymmHom hM e he hW).app V hV
      left_inv := gluedSymmHom_gluedHom hM hN e he hW V hV
      right_inv := gluedHom_gluedSymmHom hM hN e he hW V hV }
  naturality hV hWV s := (gluedHom hN e he hW).naturality hV hWV s

/-- Over an open contained in a member of the family, the glued isomorphism is that member's. -/
public theorem glueLE_app_of_le {W : Opens X} (hW : W ≤ ⨆ i, U i) {i : ι} {V : Opens X}
    (hVW : V ≤ W) (hVi : V ≤ U i) (s : M.obj (op V)) :
    (glueLE hM hN e he hW).app V hVW s = (e i).app V hVi s :=
  gluedHom_app_of_le hN e he hW hVW hVi s

/-- Over an open contained in a member of the family, the inverse of the glued isomorphism is that
member's. -/
public theorem glueLE_symm_app_of_le {W : Opens X} (hW : W ≤ ⨆ i, U i) {i : ι} {V : Opens X}
    (hVW : V ≤ W) (hVi : V ≤ U i) (t : N.obj (op V)) :
    ((glueLE hM hN e he hW).app V hVW).symm t = ((e i).app V hVi).symm t :=
  gluedSymmHom_app_of_le hM e he hW hVW hVi t

end Glue

end LocalModuleEquiv

end TopCat.Sheaf

end
