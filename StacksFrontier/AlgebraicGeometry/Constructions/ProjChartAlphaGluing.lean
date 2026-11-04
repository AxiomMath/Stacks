module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjSectionsUniqueness
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Basic
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Glueing an isomorphism of invertible modules out of matching trivialising sections

Let `Y` be a scheme and let `M` and `L` be invertible `𝒪_Y`-modules. Suppose given a family of
global sections `m i` of `M`, a family of global sections `t i` of `L`, and a family of opens
`W i` covering `Y` on which `m i` and `t i` are both nonvanishing, so that `m i` trivialises `M`
and `t i` trivialises `L` over `W i` (Stacks Tag 01CY). On `W i` the two trivialisations compose
into an isomorphism of sections `α_i : Γ(M, V) ≃ Γ(L, V)`, `V ≤ W i`, pinned by
`α_i (m i|_V) = t i|_V`: this is the per-chart isomorphism. The `α_i` glue to a global
isomorphism `α : M ≅ L` with `α (m i) = t i` precisely when the two families have the *same*
transition functions, which is the condition `Matching` below.

This is the construction of the isomorphism `α` in the existence half of
[Stacks, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8), extracted from everything about
`Proj`. There `M = φ⁎𝒪_{U_d}(d)`, `m f` is the pullback of the degree-`d` section attached to
`f ∈ S_d`, `t f = ψ(f)`, and `W f` is the chart of `f`; the source's sentence "the `α_f` agree
because the regular functions `s/s'` and `ψ_{(f')}(f/f')` agree" is exactly `Matching`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartAlpha.Matching`: two families of trivialising sections
  **match** when `m i / m j` and `t i / t j` are one and the same regular function on `W j`.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.localApp`: **the per-chart isomorphism `α_i`**, the
  composite of the trivialisation of `M` by `m i` with the inverse of the trivialisation of `L`
  by `t i`, as a linear equivalence on sections over an open inside `W i`.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.localHom`: the same, packaged as a local morphism of
  sheaves of modules on `W i` in the sense of `TopCat.Sheaf.LocalModuleHom`.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.glueHom`: the glued morphism `M ⟶ L`.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.glueIso`: **the glued isomorphism `α : M ≅ L`.**

## Main results

* `Stacks.AlgebraicGeometry.ProjChartAlpha.localApp_eq_of_eq_smul` and
  `Stacks.AlgebraicGeometry.ProjChartAlpha.localApp_resTop`: `α_i` carries `a · m i|_V` to
  `a · t i|_V`; in particular it carries `m i|_V` to `t i|_V`, which is how the source pins it.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.glueHom_app_of_le`: over an open inside `W i` the
  glued morphism *is* `α_i`.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.glueIso_hom_app_top`: **the normalisation.**
  `α (m i) = t i` for every `i`, an identity of global sections. This is the shape consumed by
  `Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq`, so the isomorphism built here
  is the one that uniqueness statement determines.
* `Stacks.AlgebraicGeometry.ProjChartAlpha.eq_glueIso`: consequently `α` is the only isomorphism
  with that normalisation.

## Implementation notes

**Glueing morphisms of sheaves of modules is not reproved here.** That morphisms of sheaves of
`𝒪`-modules glue over an open covering — the morphism half of the sheaf-of-modules case of Stacks
Tag 00AN — is `TopCat.Sheaf.existsUnique_hom_of_localModuleHom`, with the glued morphism itself
available as data in `TopCat.Sheaf.LocalModuleHom.gluedHom`
(`StacksFrontier/Topology/Sheaves/Glueing/OModuleMapGluing.lean`). The passage from there to
`Y.Modules` costs nothing: `Y.Modules` is `SheafOfModules Y.ringCatSheaf` by definition, a
morphism of which is a morphism of the underlying presheaves of modules together with no further
data, and `Y.ringCatSheaf` is a sheaf on `Opens Y` for `Opens.grothendieckTopology`, which is the
topology `TopCat.Sheaf.LocalModuleHom` works over. So `glueHom` is one constructor application.

**Why `Matching` is stated over `W j` and not over `W i ⊓ W j`.** Agreement of the `α_i` on
overlaps only needs the transition functions to agree on `W i ⊓ W j`, and that weaker hypothesis
does produce a morphism `M ⟶ L`. It does *not* produce the normalisation `α (m i) = t i`: the
value of `α (m i)` on `W j` is `(m i / m j) · t j`, an identity on all of `W j`, and off `W i`
there is nothing to compare it with. Since `W j ≤ Y_{m j}`, the ratio `m i / m j` is a regular
function on the whole of `W j` whatever `i` is, so asking for the agreement there is not asking
for more than is available; it is asking for it where it is needed. `Matching` is visibly
symmetric in the two families, which is what makes the inverse of `α` another instance of the
same construction rather than a separate argument.

**The transition function is not divided out.** `Matching` asserts the existence of a common
scalar `c` rather than the equality of two ratios. The two are equivalent — the ratio is unique
by `Stacks.NonvanishingSpelling.bijective_smul` — but the existential form is what a caller can
supply directly, and `localApp_eq_of_eq_smul` consumes it without ever naming a ratio.

**Nothing is transported along a unitor.** `M` and `L` are arbitrary invertible modules; no
tensor power, and no identification of `L` with `L^{⊗ 1}`, appears.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.TensorPowerTrivialize (resTop trivEquiv)
open Stacks.NonvanishingOpen (nonvanishingOpen)

namespace Stacks.AlgebraicGeometry.ProjChartAlpha

universe u

variable {Y : Scheme.{u}} {M L : Y.Modules} {ι : Type u}

/-! ### Matching families of trivialising sections -/

/-- Two families of global sections, `m i` of `M` and `t i` of `L`, **match** on a family of
opens `W` when for all `i` and `j` the restrictions of `m i` and of `t i` to `W j` are one and
the same multiple of the restrictions of `m j` and of `t j`.

When `W j` lies inside the nonvanishing open of `m j` and inside that of `t j`, both multiples
exist and are unique, so the condition says exactly that the transition functions `m i / m j`
and `t i / t j` agree. This is the hypothesis under which the per-chart isomorphisms glue, and it
is the Stacks Tag 01N8 sentence "the `α_f` agree because the regular functions `s/s'` and
`ψ_{(f')}(f/f')` agree". -/
def Matching (m : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤)) (W : ι → Y.Opens) : Prop :=
  ∀ i j : ι, ∃ c : Γ(Y, W j),
    resTop M (m i) (W j) = c • resTop M (m j) (W j) ∧
      resTop L (t i) (W j) = c • resTop L (t j) (W j)

/-- Matching is symmetric in the two families: the condition is a conjunction of two clauses that
are exchanged by swapping `(M, m)` with `(L, t)`. -/
theorem Matching.symm {m : ι → Γ(M, ⊤)} {t : ι → Γ(L, ⊤)} {W : ι → Y.Opens}
    (h : Matching m t W) : Matching t m W :=
  fun i j => (h i j).imp fun _ hc => ⟨hc.2, hc.1⟩

section Invertible

variable [Stacks.Ample.IsInvertibleModule Y M] [Stacks.Ample.IsInvertibleModule Y L]

/-! ### The per-chart isomorphism -/

/-- **The per-chart isomorphism `α_i` on sections.** Over an open `V` on which the global section
`m` of `M` and the global section `t` of `L` are both nonvanishing, both modules are trivialised
(Stacks Tag 01CY) and `α_i` is the composite: divide by `m`, multiply by `t`. It is a
`Γ(Y, V)`-linear equivalence `Γ(M, V) ≃ Γ(L, V)` because each half is one. -/
def localApp (m : Γ(M, ⊤)) (t : Γ(L, ⊤)) {V : Y.Opens}
    (hM : V ≤ nonvanishingOpen Y M m) (hL : V ≤ nonvanishingOpen Y L t) :
    Γ(M, V) ≃ₗ[Γ(Y, V)] Γ(L, V) :=
  (trivEquiv M m hM).symm.trans (trivEquiv L t hL)

/-- **`α_i` multiplies the ratio back by `t`.** A section written as `a · m|_V` goes to
`a · t|_V`; by uniqueness of the ratio this determines `α_i`. -/
theorem localApp_eq_of_eq_smul {m : Γ(M, ⊤)} {t : Γ(L, ⊤)} {V : Y.Opens}
    (hM : V ≤ nonvanishingOpen Y M m) (hL : V ≤ nonvanishingOpen Y L t) {x : Γ(M, V)}
    {a : Γ(Y, V)} (hx : x = a • resTop M m V) :
    localApp m t hM hL x = a • resTop L t V := by
  have ha : (trivEquiv M m hM).symm x = a :=
    (LinearEquiv.symm_apply_eq _).mpr (hx.trans rfl)
  simp only [localApp, LinearEquiv.trans_apply, ha]
  rfl

/-- **`α_i` sends the trivialising section of `M` to the trivialising section of `L`.** This is
the normalisation by which the source pins `α_f`: it "sends the pullback of the trivialising
section `f` to `s`". -/
theorem localApp_resTop (m : Γ(M, ⊤)) (t : Γ(L, ⊤)) {V : Y.Opens}
    (hM : V ≤ nonvanishingOpen Y M m) (hL : V ≤ nonvanishingOpen Y L t) :
    localApp m t hM hL (resTop M m V) = resTop L t V := by
  rw [localApp_eq_of_eq_smul hM hL (a := 1) (one_smul _ _).symm, one_smul]

/-- `α_i` commutes with restriction to a smaller open: the ratio of a restricted section is the
restriction of the ratio. -/
theorem map_localApp {m : Γ(M, ⊤)} {t : Γ(L, ⊤)} {V V' : Y.Opens}
    (hM : V ≤ nonvanishingOpen Y M m) (hL : V ≤ nonvanishingOpen Y L t) (hV : V' ≤ V)
    (x : Γ(M, V)) :
    L.presheaf.map (homOfLE hV).op (localApp m t hM hL x) =
      localApp m t (hV.trans hM) (hV.trans hL) (M.presheaf.map (homOfLE hV).op x) := by
  set a : Γ(Y, V) := (trivEquiv M m hM).symm x with ha
  have hx : x = a • resTop M m V := (Stacks.TensorPowerTrivialize.trivEquiv_symm_smul M m hM x).symm
  have hx' : M.presheaf.map (homOfLE hV).op x =
      Y.presheaf.map (homOfLE hV).op a • resTop M m V' := by
    rw [hx, Stacks.TensorPowerTrivialize.map_smul_resTop]
  rw [localApp_eq_of_eq_smul hM hL hx, localApp_eq_of_eq_smul _ _ hx',
    Stacks.TensorPowerTrivialize.map_smul_resTop]

/-- A relation `n = c • n'` between restricted sections persists on a smaller open. -/
private theorem resTop_eq_smul_of_le {N : Y.Modules} {n n' : Γ(N, ⊤)} {V V' : Y.Opens}
    (hV : V ≤ V') {c : Γ(Y, V')} (h : resTop N n V' = c • resTop N n' V') :
    resTop N n V = Y.presheaf.map (homOfLE hV).op c • resTop N n' V := by
  rw [← Stacks.TensorPowerTrivialize.map_smul_resTop, ← h,
    Stacks.TensorPowerTrivialize.res_resTop]

/-- **The per-chart isomorphisms agree where two charts meet.** Over an open inside both `W i`
and `W j`, matching of the two families makes `α_i` and `α_j` the same map: a section is
`a · m i|_V`, hence `(a · c) · m j|_V` for the common transition function `c`, and the two values
`a · t i|_V` and `(a · c) · t j|_V` agree for the same reason. -/
theorem localApp_congr {m : ι → Γ(M, ⊤)} {t : ι → Γ(L, ⊤)} {W : ι → Y.Opens}
    (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i))
    (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i)) (hmatch : Matching m t W) (i j : ι)
    {V : Y.Opens} (hVi : V ≤ W i) (hVj : V ≤ W j) (x : Γ(M, V)) :
    localApp (m i) (t i) (hVi.trans (hM i)) (hVi.trans (hL i)) x =
      localApp (m j) (t j) (hVj.trans (hM j)) (hVj.trans (hL j)) x := by
  obtain ⟨c, hcM, hcL⟩ := hmatch i j
  set c' : Γ(Y, V) := Y.presheaf.map (homOfLE hVj).op c with hc'
  have hmres := resTop_eq_smul_of_le hVj hcM
  have htres := resTop_eq_smul_of_le hVj hcL
  set a : Γ(Y, V) := (trivEquiv M (m i) (hVi.trans (hM i))).symm x with ha
  have hx : x = a • resTop M (m i) V :=
    (Stacks.TensorPowerTrivialize.trivEquiv_symm_smul M (m i) (hVi.trans (hM i)) x).symm
  have hxj : x = (a * c') • resTop M (m j) V := by
    rw [hx, hmres, mul_smul]
  rw [localApp_eq_of_eq_smul _ _ hx, localApp_eq_of_eq_smul _ _ hxj, htres, mul_smul]

/-! ### The local morphisms of sheaves of modules -/

/-- **The per-chart isomorphism `α_i` as a local morphism of sheaves of modules on `W i`.** This
is the datum that `TopCat.Sheaf.LocalModuleHom.gluedHom` glues; its naturality is
`map_localApp`. -/
def localHom (m : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤)) (W : ι → Y.Opens)
    (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i))
    (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i)) (i : ι) :
    TopCat.Sheaf.LocalModuleHom M.val L.val (W i) where
  app _V hV :=
    ModuleCat.ofHom (localApp (m i) (t i) (hV.trans (hM i)) (hV.trans (hL i))).toLinearMap
  naturality _hV hV' s := (map_localApp _ _ hV' s).symm

/-- On an open `V ≤ W i`, the `i`-th local morphism acts on sections as `localApp`. -/
@[simp] theorem localHom_app_apply (m : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤)) (W : ι → Y.Opens)
    (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i))
    (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i)) (i : ι) {V : Y.Opens} (hV : V ≤ W i)
    (x : Γ(M, V)) :
    (localHom m t W hM hL i).app V hV x =
      localApp (m i) (t i) (hV.trans (hM i)) (hV.trans (hL i)) x :=
  rfl

/-- The compatibility hypothesis of `TopCat.Sheaf.existsUnique_hom_of_localModuleHom`, discharged
by `localApp_congr`. -/
theorem localHom_app_eq {m : ι → Γ(M, ⊤)} {t : ι → Γ(L, ⊤)} {W : ι → Y.Opens}
    (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i))
    (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i)) (hmatch : Matching m t W) (i j : ι)
    (V : Y.Opens) (hVi : V ≤ W i) (hVj : V ≤ W j) :
    (localHom m t W hM hL i).app V hVi = (localHom m t W hM hL j).app V hVj :=
  ModuleCat.hom_ext (LinearMap.ext (localApp_congr hM hL hmatch i j hVi hVj))

/-- Each `m i` spans `M` over `W i`, in the sense of
`Stacks.AlgebraicGeometry.ProjSectionsUnique.SpansOver`: `W i` lies inside the nonvanishing open
of `m i`, where `m i` is a basis by Stacks Tag 01CY. -/
theorem spansOver_of_le (m : ι → Γ(M, ⊤)) (W : ι → Y.Opens)
    (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i)) (i : ι) :
    Stacks.AlgebraicGeometry.ProjSectionsUnique.SpansOver M (m i) (W i) :=
  fun V hV x =>
    Stacks.AlgebraicGeometry.ProjSectionsUnique.spansOver_nonvanishingOpen Y M (m i) V
      (hV.trans (hM i)) x

/-- The nonvanishing opens of the `t i` cover `Y`, since they contain the `W i`. This is the
generation hypothesis of Section 27.12 in the geometric form the uniqueness half uses. -/
theorem iSup_nonvanishingOpen_eq_top (t : ι → Γ(L, ⊤)) (W : ι → Y.Opens)
    (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i)) (hcover : ⨆ i, W i = ⊤) :
    ⨆ i, nonvanishingOpen Y L (t i) = ⊤ :=
  top_le_iff.mp (le_trans hcover.ge (iSup_mono hL))

/-! ### The glued morphism -/

variable (m : ι → Γ(M, ⊤)) (t : ι → Γ(L, ⊤)) (W : ι → Y.Opens)
  (hM : ∀ i, W i ≤ nonvanishingOpen Y M (m i))
  (hL : ∀ i, W i ≤ nonvanishingOpen Y L (t i))
  (hcover : ⨆ i, W i = ⊤) (hmatch : Matching m t W)

/-- **The glued morphism `M ⟶ L`.** The per-chart isomorphisms agree on overlaps and the `W i`
cover `Y`, so they glue, by `TopCat.Sheaf.LocalModuleHom.gluedHom` — morphisms of sheaves of
`𝒪`-modules glue over an open covering. A morphism of `Y.Modules` is a morphism of the underlying
presheaves of modules, so no further data is needed. -/
def glueHom : M ⟶ L :=
  ⟨TopCat.Sheaf.LocalModuleHom.gluedHom hcover L.isSheaf (localHom m t W hM hL)
    (localHom_app_eq hM hL hmatch)⟩

/-- **Over an open inside `W i` the glued morphism is `α_i`.** -/
theorem glueHom_app_of_le (i : ι) {V : Y.Opens} (hV : V ≤ W i) (x : Γ(M, V)) :
    (glueHom m t W hM hL hcover hmatch).app V x =
      localApp (m i) (t i) (hV.trans (hM i)) (hV.trans (hL i)) x :=
  congrArg (fun g : M.val.obj (op V) ⟶ L.val.obj (op V) => g x)
    (TopCat.Sheaf.LocalModuleHom.gluedHom_app hcover L.isSheaf (localHom m t W hM hL)
      (localHom_app_eq hM hL hmatch) i V hV)

/-- **The normalisation of the glued morphism**, as an identity of global sections: it sends
`m i` to `t i`.

Both sides are compared on the covering `W`. On `W j` the glued morphism is `α_j`, which carries
`m i|_{W j} = c · m j|_{W j}` to `c · t j|_{W j}`, and that is `t i|_{W j}` by the second clause
of `Matching`. -/
theorem glueHom_app_top (i : ι) : (glueHom m t W hM hL hcover hmatch).app ⊤ (m i) = t i := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf L.isSheaf W
    (fun _ => le_top) hcover.ge fun j => ?_
  obtain ⟨c, hcM, hcL⟩ := hmatch i j
  have key : resTop L ((glueHom m t W hM hL hcover hmatch).app ⊤ (m i)) (W j) =
      resTop L (t i) (W j) := by
    rw [show resTop L ((glueHom m t W hM hL hcover hmatch).app ⊤ (m i)) (W j) =
          (glueHom m t W hM hL hcover hmatch).app (W j) (resTop M (m i) (W j)) from
        Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app _ le_top (m i),
      glueHom_app_of_le m t W hM hL hcover hmatch j le_rfl,
      localApp_eq_of_eq_smul _ _ hcM, ← hcL]
  exact key

/-! ### The glued isomorphism -/

/-- **The glued isomorphism `α : M ≅ L` of Stacks Tag 01N8.** The inverse is the same
construction with the two families exchanged, which is legitimate because `Matching` is
symmetric; the two composites are the identity because they fix the spanning families `m` and
`t`. -/
def glueIso : M ≅ L where
  hom := glueHom m t W hM hL hcover hmatch
  inv := glueHom t m W hL hM hcover hmatch.symm
  hom_inv_id := by
    refine Stacks.AlgebraicGeometry.ProjSectionsUnique.hom_ext_of_spansOver m W hcover
      (spansOver_of_le m W hM) fun i => ?_
    rw [Scheme.Modules.Hom.comp_app]
    change (glueHom t m W hL hM hcover hmatch.symm).app ⊤
      ((glueHom m t W hM hL hcover hmatch).app ⊤ (m i)) = _
    rw [glueHom_app_top m t W hM hL hcover hmatch i,
      glueHom_app_top t m W hL hM hcover hmatch.symm i]
    simp
  inv_hom_id := by
    refine Stacks.AlgebraicGeometry.ProjSectionsUnique.hom_ext_of_spansOver t W hcover
      (spansOver_of_le t W hL) fun i => ?_
    rw [Scheme.Modules.Hom.comp_app]
    change (glueHom m t W hM hL hcover hmatch).app ⊤
      ((glueHom t m W hL hM hcover hmatch.symm).app ⊤ (t i)) = _
    rw [glueHom_app_top t m W hL hM hcover hmatch.symm i,
      glueHom_app_top m t W hM hL hcover hmatch i]
    simp

/-- The forward morphism of `glueIso` is `glueHom m t W`. -/
@[simp] theorem glueIso_hom : (glueIso m t W hM hL hcover hmatch).hom =
    glueHom m t W hM hL hcover hmatch := rfl

/-- The inverse of `glueIso` is the glued morphism `glueHom t m W` with the families exchanged. -/
@[simp] theorem glueIso_inv : (glueIso m t W hM hL hcover hmatch).inv =
    glueHom t m W hL hM hcover hmatch.symm := rfl

/-- **The normalisation of `α`**, in the shape
`Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq` consumes: `α (m i) = t i` for
every `i`. -/
theorem glueIso_hom_app_top (i : ι) :
    (glueIso m t W hM hL hcover hmatch).hom.app ⊤ (m i) = t i :=
  glueHom_app_top m t W hM hL hcover hmatch i

/-- **`α` is the unique isomorphism `M ≅ L` with `α (m i) = t i`.** Existence is `glueIso`;
uniqueness is `Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq`, whose covering
hypothesis is `iSup_nonvanishingOpen_eq_top`. So the isomorphism constructed here is exactly the
one the uniqueness half of Stacks Tag 01N8 pins down. -/
theorem eq_glueIso (β : M ≅ L) (hβ : ∀ i, β.hom.app ⊤ (m i) = t i) :
    β = glueIso m t W hM hL hcover hmatch :=
  Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq
    (iSup_nonvanishingOpen_eq_top t W hL hcover) β _ hβ
    (glueIso_hom_app_top m t W hM hL hcover hmatch)

end Invertible

end Stacks.AlgebraicGeometry.ProjChartAlpha

end
