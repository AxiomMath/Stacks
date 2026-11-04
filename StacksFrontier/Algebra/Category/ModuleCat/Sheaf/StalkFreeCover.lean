module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# A finitely presented sheaf of modules with a free stalk is free near that point

Let `(X, 𝒪_X)` be a ringed space and let `M` be a sheaf of `𝒪_X`-modules of finite
presentation. If the stalk `M_x` is a free `𝒪_{X,x}`-module of finite rank, then `M` is free of
that rank on an open neighbourhood of `x`. This is Stacks Tag 0B8J.

## Main definitions

* `Stacks.SheafOfModules.freeProj`, `freeCoord` and `freeMk`: coordinates on
  `SheafOfModules.free ι` for a finite index type `ι`. These exist because for finite `ι` the
  coproduct `free ι = ∐ unit` is also a product, which is recorded here in the usable form
  `id_free_eq_sum : 𝟙 (free ι) = ∑ i, freeProj i ≫ ιFree i`.
* `Stacks.SheafOfModules.res` and `resR`: restriction of a section of a sheaf of modules, resp.
  of the sheaf of rings, along a morphism of the site, with the target read as a module over
  `R(V)` rather than as a restriction of scalars.
* `Stacks.SheafOfModules.overSection` and `freeToOver`: a family of sections of `M` over `U`
  read as global sections of `M.over U`, and the induced morphism `free ι ⟶ M.over U`.
* `Stacks.SheafOfModules.ofCoordsOver` and `coordsOver`: the coordinates of a section of
  `free ι` over an object `V` of the slice site at `U`, with the scalars read in `R(V.left)`
  rather than in the structure sheaf `(R.over U).obj.obj (op V)` of the slice site.
  `Stacks.SheafOfModules.ofCoords` and `coords` are the same layer indexed by a morphism
  `W ⟶ U` instead of by an object of the slice site.
* `Stacks.SheafOfModules.LocalPresentation`: section-level finite presentation data for `M` on
  a neighbourhood of a point — finitely many generating sections, finitely many relations
  between them, and the statements that the generators generate and the relations generate all
  relations, both locally at every point.
* `Stacks.SheafOfModules.germ`: the germ at `x` of a section of a sheaf of modules.
* `Stacks.SheafOfModules.freeMat`: the matrix of a morphism between finite free sheaves of
  modules over the slice site at an open `U`.

## Main results

* `Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free` is Tag 0B8J.
* `Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis` is the same statement phrased
  with a `Module.Basis` of the stalk instead of a linear equivalence with a finitely supported
  function type.
* `Stacks.SheafOfModules.nonempty_localPresentation` turns the Mathlib predicate
  `SheafOfModules.IsFinitePresentation` into section-level presentation data near a point; it
  realises the content of Tag 01BN.
* `Stacks.SheafOfModules.exists_chart` is the spreading step: near a point at which the stalk
  is free it produces sections realising a basis, together with matrices `A`, `B` expressing
  those sections through the presentation's generators and conversely, and the two identities
  `A * B = 1` and `rel * B = 0`.
* `Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj`: a finite family of sections
  trivialises `M` on `U` as soon as taking `R(V)`-combinations of it is injective for every
  open `V ≤ U` and surjective after shrinking around each point.
* `Stacks.SheafOfModules.exists_kernel_section`: kernels of morphisms of sheaves of modules are
  computed sectionwise.

## Implementation notes

The proof deliberately avoids Tag 01BP ("the kernel of a map from a finite free module onto a
finitely presented module is of finite type"), which would otherwise be the natural route via
Tags 01B8 and 01B9. Instead the finite presentation is unpacked into explicit matrices over the
sections of the structure sheaf, and the whole argument is the following computation. Write the
chosen sections `s` through the generators `u` as `s = A·u`, the generators through the chosen
sections as `u = B·s`, and let `rel` be the relation matrix. Because the germs of `s` at `x`
form a basis of the stalk, the identities `A·B = 1` and `rel·B = 0` hold at `x`, hence on a
neighbourhood, since they involve only finitely many sections. On that neighbourhood `A·B = 1`
gives injectivity of `c ↦ ∑ cᵢ sᵢ` on sections and `rel·B = 0` turns every local relation among
the generators into the zero relation among the `s`, which is what makes the argument close.
Surjectivity is only local, so the final morphism is shown to be an epimorphism through local
surjectivity rather than through gluing; monomorphism plus epimorphism gives an isomorphism
because the category of sheaves of modules is abelian.

Two features of the site `Opens X` are used throughout and are what makes the bookkeeping
tractable. First, the slice site `Over U` is definitionally transparent: for `V : Over U` the
module `(M.over U).val.obj (op V)` *is* `M.val.obj (op V.left)`, with the same restriction maps.
Second, any two morphisms `V ⟶ U` of opens are definitionally equal, so restriction maps compose
freely and no coherence data is needed; this is why `res` can be used with whichever morphism is
at hand. Only the second of these is special to `Opens X`: the statements are given in two
layers, one with coordinates in the structure sheaf of the slice site (`freeMk`, `freeCoord`)
and one with coordinates in `R(V)` (`ofCoordsOver`, `coordsOver`, `ofCoords`, `coords`), because
`rw` works up to a transparency setting under which `(R.over U).obj.obj (op V)` and
`R.obj.obj (op V.left)` are not interchangeable — and **both layers are available over an
arbitrary site**, in `section Slice`. Tag 0B8J itself still lives over `Opens X`, since the
spreading argument needs points.

**What the second layer can and cannot say.** Element-level statements respell freely: the two
defining equations, the round trips, the naturality `coordsOver_map`, the additivity
`coordsOver_add` and the evaluation formula `freeToOver_app_ofCoordsOver` all hold with the
scalars in `R(V.left)`, each proved by `:=` or `exact`, which tolerate the definitional
equality. What does **not** respell is the *scalar action itself*: `a • e` for
`a : ToType (R.obj.obj (op V.left))` and `e : ToType ((free ι).val.obj (op V))` has no `HSMul`
instance, because instance synthesis will not unfold `(R.over U).obj.obj (op V)` to reach it.
**This obstruction is narrow, and it is resolved.** The
obstruction is purely a failure of instance *synthesis* when the ring is a metavariable; where
both types are already fixed, the crossing is definitional at default transparency. So the cure
is not bespoke surgery but Mathlib's own change-of-rings along the identity:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction` defines `overBase` as
`PresheafOfModules.restrictScalars` applied to the identity morphism of ring presheaves
`(Over.forget U).op ⋙ R.obj ⟶ (R.over U).obj`, which changes only the carrier's *spelling*, so
exactly one `Module` instance is ever found. It must be a `def` with an ascribed type and not an
`abbrev`, since a reducible wrapper is unfolded by instance search and loses the instance again.

Consequently `coordsOver_smul` and `coordsOver` as a `LinearEquiv` over `R(V.left)` are
`Stacks.SheafOfModules.coordsOver_smul` and `Stacks.SheafOfModules.coordsOverLinearEquiv` in that
file. `Stacks.SheafOfModules.relationsPresheaf` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections` is still the wrapper-carrying
form, and it is now *identified* with the kernel by `relationsPresheafIso`.

One spelling pitfall remains: mixing the two spellings inside a product fails
at `HMul`, not at `rw` — stating `coordsOver V (b • e) i = b * coordsOver V e i` with `b`
slice-spelled reports `failed to synthesize HMul …`. Put the respelling *inside* the smul
instead, which is one application of `map_smul`.

No universe is narrowed: the general sections are stated for `C : Type u'` with
`Category.{v} C` and `R : Sheaf J RingCat.{u}`, three independent universes, and the `Opens X`
section for `SheafOfModules.{u} R` with `R : TopCat.Sheaf RingCat.{u} X` and `X : TopCat.{u}`,
which is the single universe the site `Opens X` forces.

**Which sheafification hypotheses the slice layer carries.** `HasWeakSheafify (J.over U)` and
`(J.over U).WEqualsLocallyBijective` for the *one* object `U` at hand, written as instance
binders on each declaration rather than as `∀ Z : C` section variables. The `∀ Z` form is
weaker to state but synthesizes to a lambda that `rw` will not match against a second synthesis
of the same instance, which silently breaks `rw [ofCoords_coords]` and `rw [coords_map]` in the
`Opens X` proofs below. The per-object form is also the more general one.

## References

* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 01BN](https://stacks.math.columbia.edu/tag/01BN)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u v u'

namespace Stacks.SheafOfModules

/-! ### Coordinates on a free sheaf of modules with finite index type -/

section FreeCoords

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- The unit section of `SheafOfModules.unit S` over an object `V`. -/
def unitOne (V : Cᵒᵖ) : ToType ((unit S).val.obj V) := (1 : ToType (S.obj.obj V))

/-- An element of `S(V)` read as a section of `SheafOfModules.unit S` over `V`. -/
def toUnit (V : Cᵒᵖ) (c : ToType (S.obj.obj V)) : ToType ((unit S).val.obj V) := c

/-- Scalar multiplication on `toUnit` sections is multiplication in `S(V)`. -/
lemma toUnit_smul (V : Cᵒᵖ) (a c : ToType (S.obj.obj V)) :
    a • toUnit (S := S) V c = toUnit (S := S) V (a * c) := rfl

/-- `toUnit` commutes with finite sums. -/
lemma toUnit_sum {κ : Type*} (V : Cᵒᵖ) (t : Finset κ) (c : κ → ToType (S.obj.obj V)) :
    toUnit (S := S) V (∑ j ∈ t, c j) = ∑ j ∈ t, toUnit (S := S) V (c j) := rfl

/-- The morphism `unit S ⟶ N` corresponding to a global section `t` sends the unit section
over `V` to the value of `t` over `V`. -/
lemma unitHomEquiv_symm_app_unitOne {N : SheafOfModules.{u} S} (t : N.sections) (V : Cᵒᵖ) :
    (N.unitHomEquiv.symm t).val.app V (unitOne V) = t.eval V := by
  rw [show (N.unitHomEquiv.symm t).val.app V (unitOne V)
    = (N.unitHomEquiv (N.unitHomEquiv.symm t)).eval V from
      (unitHomEquiv_apply_coe N _ V).symm, N.unitHomEquiv.apply_symm_apply]

/-- The zero morphism of sheaves of modules sends every section to zero. -/
lemma zero_app_apply {N P : SheafOfModules.{u} S} (V : Cᵒᵖ) (e : ToType (N.val.obj V)) :
    (0 : N ⟶ P).val.app V e = 0 := rfl

/-- A finite sum of morphisms of sheaves of modules acts on sections as the sum of the actions. -/
lemma app_sum {N P : SheafOfModules.{u} S} {ι : Type*} (t : Finset ι) (f : ι → (N ⟶ P)) (V : Cᵒᵖ)
    (e : ToType (N.val.obj V)) :
    (∑ i ∈ t, f i).val.app V e = ∑ i ∈ t, (f i).val.app V e := by
  classical
  induction t using Finset.induction with
  | empty => exact zero_app_apply V e
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; simp

/-- The section `toUnit V c` is `c` times the unit section. -/
lemma toUnit_eq_smul (V : Cᵒᵖ) (c : ToType (S.obj.obj V)) :
    toUnit (S := S) V c = c • unitOne (S := S) V :=
  show (c : ToType (S.obj.obj V)) = c * 1 from (mul_one c).symm

/-- A morphism out of `unit S` is determined over `V` by the image of the unit section. -/
lemma app_unit_eq {N : SheafOfModules.{u} S} (f : unit S ⟶ N) (V : Cᵒᵖ)
    (c : ToType (S.obj.obj V)) :
    f.val.app V (toUnit V c) = c • f.val.app V (unitOne V) := by
  rw [toUnit_eq_smul, (f.val.app V).hom.map_smul c (unitOne (S := S) V)]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The `i`-th coordinate projection of the free sheaf of modules on `ι`. -/
noncomputable def freeProj {ι : Type u} [DecidableEq ι] (i : ι) : free (R := S) ι ⟶ unit S :=
  (freeHomEquiv _).symm fun j => (unit S).unitHomEquiv (if j = i then 𝟙 _ else 0)

/-- The `j`-th inclusion followed by the `i`-th projection is the identity if `j = i` and zero
otherwise. -/
lemma ιFree_comp_freeProj {ι : Type u} [DecidableEq ι] (i j : ι) :
    ιFree (R := S) j ≫ freeProj i = if j = i then 𝟙 _ else 0 := by
  refine (unit S).unitHomEquiv.injective ?_
  rw [show (unit S).unitHomEquiv (ιFree j ≫ freeProj i)
    = freeHomEquiv (unit S) (freeProj i) j from rfl, freeProj,
    (freeHomEquiv (unit S)).apply_symm_apply]

/-- The `i`-th inclusion followed by the `i`-th projection is the identity. -/
lemma ιFree_comp_freeProj_self {ι : Type u} [DecidableEq ι] (i : ι) :
    ιFree (R := S) i ≫ freeProj i = 𝟙 _ := by rw [ιFree_comp_freeProj]; simp

/-- The `j`-th inclusion followed by the `i`-th projection is zero for `j ≠ i`. -/
lemma ιFree_comp_freeProj_of_ne {ι : Type u} [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    ιFree (R := S) j ≫ freeProj i = 0 := by rw [ιFree_comp_freeProj]; simp [h]

/-- For finite `ι`, the identity of `free ι` is the sum of the composites of the coordinate
projections with the inclusions. -/
lemma id_free_eq_sum {ι : Type u} [DecidableEq ι] [Fintype ι] :
    𝟙 (free (R := S) ι) = ∑ i : ι, freeProj i ≫ ιFree i := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan ι) _ _ fun j => ?_
  have h : ∀ f : free (R := S) ι ⟶ free (R := S) ι,
      (freeCofan (R := S) ι).inj j ≫ f = ιFree j ≫ f := fun _ => rfl
  rw [h, h, Category.comp_id, Preadditive.comp_sum,
    Finset.sum_eq_single j (fun b _ hb => by
      rw [← Category.assoc, ιFree_comp_freeProj_of_ne (Ne.symm hb), zero_comp])
      (fun h => absurd (Finset.mem_univ j) h), ← Category.assoc, ιFree_comp_freeProj_self,
    Category.id_comp]

/-- The coordinates of a section of a free sheaf of modules on a finite index type. -/
noncomputable def freeCoord {ι : Type u} [DecidableEq ι] (V : Cᵒᵖ)
    (e : ToType ((free (R := S) ι).val.obj V)) (i : ι) : ToType (S.obj.obj V) :=
  (freeProj i).val.app V e

/-- The section of a free sheaf of modules with prescribed coordinates. -/
noncomputable def freeMk {ι : Type u} [Fintype ι] (V : Cᵒᵖ) (c : ι → ToType (S.obj.obj V)) :
    ToType ((free (R := S) ι).val.obj V) :=
  ∑ i : ι, (ιFree (R := S) i).val.app V (toUnit V (c i))

/-- Scalar multiplication of `freeMk V c` multiplies every coordinate. -/
lemma freeMk_smul {ι : Type u} [Fintype ι] (V : Cᵒᵖ) (a : ToType (S.obj.obj V))
    (c : ι → ToType (S.obj.obj V)) :
    a • freeMk (S := S) V c = freeMk (S := S) V (fun k => a * c k) := by
  rw [freeMk, freeMk, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (ιFree (R := S) i).val.app V |>.hom.map_smul a (toUnit V (c i)), toUnit_smul]

/-- A finite sum of sections `freeMk V (c j)` is the section with the summed coordinates. -/
lemma freeMk_sum {ι : Type u} [Fintype ι] {κ : Type*} (V : Cᵒᵖ) (t : Finset κ)
    (c : κ → ι → ToType (S.obj.obj V)) :
    ∑ j ∈ t, freeMk (S := S) V (c j) = freeMk (S := S) V (fun k => ∑ j ∈ t, c j k) := by
  simp only [freeMk, toUnit_sum, map_sum]
  rw [Finset.sum_comm]

/-- Coordinates are compatible with the restriction maps of `free ι` and of `S`. -/
lemma freeCoord_map {ι : Type u} [DecidableEq ι] {V W : Cᵒᵖ} (m : V ⟶ W)
    (e : ToType ((free (R := S) ι).val.obj V)) (i : ι) :
    freeCoord (S := S) W ((free (R := S) ι).val.map m e) i
      = S.obj.map m (freeCoord (S := S) V e i) :=
  PresheafOfModules.naturality_apply (freeProj (S := S) i).val m e

/-- The coordinates of the section with prescribed coordinates `c` are `c`. -/
lemma freeCoord_freeMk {ι : Type u} [DecidableEq ι] [Fintype ι] (V : Cᵒᵖ)
    (c : ι → ToType (S.obj.obj V)) : freeCoord (S := S) V (freeMk V c) = c := by
  funext j
  have key : ∀ b : ι, (freeProj (S := S) j).val.app V
        ((ιFree (R := S) b).val.app V (toUnit V (c b)))
      = (ιFree (R := S) b ≫ freeProj j).val.app V (toUnit V (c b)) := fun _ => rfl
  have h0 : ∀ b ∈ (Finset.univ : Finset ι), b ≠ j → (freeProj (S := S) j).val.app V
      ((ιFree (R := S) b).val.app V (toUnit V (c b))) = 0 := by
    intro b _ hb
    rw [key b, ιFree_comp_freeProj_of_ne hb]
    exact zero_app_apply V _
  have hj : (freeProj (S := S) j).val.app V
      ((ιFree (R := S) j).val.app V (toUnit V (c j))) = c j := by
    rw [key j, ιFree_comp_freeProj_self]; rfl
  show (freeProj j).val.app V (∑ i : ι, (ιFree (R := S) i).val.app V (toUnit V (c i))) = c j
  rw [map_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j) h0, hj]

/-- A section of a finite free sheaf of modules is the section with its own coordinates. -/
lemma freeMk_freeCoord {ι : Type u} [DecidableEq ι] [Fintype ι] (V : Cᵒᵖ)
    (e : ToType ((free (R := S) ι).val.obj V)) : freeMk V (freeCoord (S := S) V e) = e :=
  calc freeMk V (freeCoord (S := S) V e)
      = ∑ i : ι, (ιFree (R := S) i).val.app V (toUnit V (freeCoord (S := S) V e i)) := rfl
    _ = (∑ i : ι, freeProj (S := S) i ≫ ιFree i).val.app V e := by
        rw [app_sum]; exact Finset.sum_congr rfl fun i _ => rfl
    _ = (SheafOfModules.Hom.val (𝟙 (free (R := S) ι))).app V e := by rw [id_free_eq_sum]
    _ = e := rfl

/-- Taking coordinates is a bijection between the sections of a finite free sheaf of modules
over an object and the families of sections of the structure sheaf. -/
lemma freeCoord_bijective {ι : Type u} [DecidableEq ι] [Finite ι] (V : Cᵒᵖ) :
    Function.Bijective (freeCoord (S := S) (ι := ι) V) := by
  cases nonempty_fintype ι
  exact Function.bijective_iff_has_inverse.2
    ⟨freeMk V, freeMk_freeCoord V, freeCoord_freeMk V⟩

/-- The coordinate description of a morphism out of a finite free sheaf of modules. -/
lemma app_freeMk {ι : Type u} [Fintype ι] {N : SheafOfModules.{u} S} (f : free ι ⟶ N) (V : Cᵒᵖ)
    (c : ι → ToType (S.obj.obj V)) :
    f.val.app V (freeMk V c) = ∑ i : ι, c i • (ιFree i ≫ f).val.app V (unitOne V) := by
  rw [freeMk, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (f.val.app V) ((ιFree (R := S) i).val.app V (toUnit V (c i)))
      = (ιFree (R := S) i ≫ f).val.app V (toUnit V (c i)) from rfl, app_unit_eq]

/-- The morphism out of `free ι` determined by a family of global sections `t` restricts along
the `i`-th inclusion to the morphism out of `unit` determined by `t i`. -/
lemma ιFree_comp_freeHomEquiv_symm {ι : Type u} {N : SheafOfModules.{u} S} (t : ι → N.sections)
    (i : ι) : ιFree i ≫ (freeHomEquiv N).symm t = N.unitHomEquiv.symm (t i) := by
  rw [show ιFree i ≫ (freeHomEquiv N).symm t
    = N.unitHomEquiv.symm (freeHomEquiv N ((freeHomEquiv N).symm t) i) from
      (unitHomEquiv_symm_freeHomEquiv_apply _ i).symm, (freeHomEquiv N).apply_symm_apply]

section Kernels

universe u₂

variable [HasSheafify J AddCommGrpCat.{u₂}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Kernels of morphisms of sheaves of modules are computed sectionwise: a section of the
source killed by the morphism comes from a section of the kernel. The universe of the module
sections is independent of the universe of the sections of the sheaf of rings, as it is for the
sheaves of modules carrying a conormal sequence. -/
lemma exists_kernel_section {N P : SheafOfModules.{u₂} S} (g : N ⟶ P) (V : Cᵒᵖ)
    (z : ToType (N.val.obj V)) (hz : g.val.app V z = 0) :
    ∃ w : ToType ((kernel g).val.obj V), (kernel.ι g).val.app V w = z := by
  have : (SheafOfModules.evaluation S V).Additive :=
    inferInstanceAs ((SheafOfModules.forget S) ⋙ PresheafOfModules.evaluation S.obj V).Additive
  let G := SheafOfModules.evaluation S V
  have hz' : (G.map g) z = 0 := hz
  let k : LinearMap.ker (ModuleCat.Hom.hom (G.map g)) := ⟨z, hz'⟩
  refine ⟨(PreservesKernel.iso G g).inv ((ModuleCat.kernelIsoKer (G.map g)).inv k), ?_⟩
  have h1 := ConcreteCategory.congr_hom (ModuleCat.kernelIsoKer_inv_kernel_ι (G.map g)) k
  have h2 := ConcreteCategory.congr_hom (PreservesKernel.iso_inv_ι G g)
    ((ModuleCat.kernelIsoKer (G.map g)).inv k)
  show (G.map (kernel.ι g)) ((PreservesKernel.iso G g).inv _) = z
  rw [show (G.map (kernel.ι g)) ((PreservesKernel.iso G g).inv
      ((ModuleCat.kernelIsoKer (G.map g)).inv k))
    = ((PreservesKernel.iso G g).inv ≫ G.map (kernel.ι g))
      ((ModuleCat.kernelIsoKer (G.map g)).inv k) from rfl, h2,
    ← ConcreteCategory.comp_apply, h1]
  rfl

end Kernels

end FreeCoords

/-! ### Restriction to a slice site, and coordinates with scalars in the base

Everything in this section is about an arbitrary site. A section of a sheaf of modules over an
object `U` is restricted along a morphism (`res`, `resR`) and read as a global section of the
slice `M.over U` (`overSection`), and the coordinates of a section of `free ι` over an object
`V` of the slice site are expressed with scalars in `S(V.left)` rather than in the structure
sheaf of the slice site (`coordsOver`, `ofCoordsOver`).

That second coordinate layer is the whole point of the section. `(S.over U).obj.obj (op V)` and
`S.obj.obj (op V.left)` are definitionally equal but *not* interchangeable for `rw` or for
instance synthesis — Lean reports "target expression is not type-correct under the `implicit`
transparency level" — so a statement that has to spell its scalars in the base, as the
sectionwise relations of Tag 03DL do, cannot be rewritten into the slice-site spelling that
`freeCoord`, `kernel` and `exists_kernel_section` use. The defining equations below cross that
boundary with `:=` and `exact`, which are defeq-tolerant, and every statement afterwards stays
on one side of it. -/

section Slice

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Restriction of a section of `M` along a morphism of the site, with the target read as an
`R(V)`-module rather than as the restriction of scalars of one. -/
noncomputable def res (M : SheafOfModules.{u} R) {U V : C} (f : V ⟶ U)
    (m : ToType (M.val.obj (op U))) : ToType (M.val.obj (op V)) :=
  M.val.map f.op m

/-- Restricting along `f` and then along `g` is restricting along `g ≫ f`. -/
lemma res_res (M : SheafOfModules.{u} R) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (m : ToType (M.val.obj (op U))) : res M g (res M f m) = res M (g ≫ f) m :=
  (M.val.map_comp_apply f.op g.op m).symm

/-- Restriction along the identity is the identity. -/
lemma res_id (M : SheafOfModules.{u} R) {U : C} (m : ToType (M.val.obj (op U))) :
    res M (𝟙 U) m = m := by
  rw [res, show (𝟙 U).op = 𝟙 (op U) from rfl]
  exact congrFun (congrArg (fun h => (ConcreteCategory.hom h : _ → _)) (M.val.map_id (op U))) m

/-- Restriction of a section of the sheaf of rings along a morphism of the site. -/
noncomputable def resR (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (a : ToType (R.obj.obj (op U))) : ToType (R.obj.obj (op V)) :=
  R.obj.map f.op a

/-- Restriction is semilinear along restriction of scalars in the sheaf of rings. -/
lemma res_smul (M : SheafOfModules.{u} R) {U V : C} (f : V ⟶ U)
    (a : ToType (R.obj.obj (op U))) (m : ToType (M.val.obj (op U))) :
    res M f (a • m) = resR R f a • res M f m :=
  M.val.map_smul f.op a m

/-- Restriction commutes with finite sums. -/
lemma res_sum (M : SheafOfModules.{u} R) {U V : C} (f : V ⟶ U) {ι : Type*}
    (t : Finset ι) (m : ι → ToType (M.val.obj (op U))) :
    res M f (∑ i ∈ t, m i) = ∑ i ∈ t, res M f (m i) :=
  map_sum (M.val.map f.op).hom m t

/-- Restriction sends zero to zero. -/
lemma res_zero (M : SheafOfModules.{u} R) {U V : C} (f : V ⟶ U) :
    res M f (0 : ToType (M.val.obj (op U))) = 0 :=
  map_zero (M.val.map f.op).hom

/-- Restriction in the sheaf of rings is multiplicative. -/
lemma resR_mul (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (a b : ToType (R.obj.obj (op U))) : resR R f (a * b) = resR R f a * resR R f b :=
  map_mul (R.obj.map f.op).hom a b

/-- Restriction in the sheaf of rings commutes with subtraction. -/
lemma resR_sub (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
    (a b : ToType (R.obj.obj (op U))) : resR R f (a - b) = resR R f a - resR R f b :=
  map_sub (R.obj.map f.op).hom a b

/-- Restriction in the sheaf of rings sends one to one. -/
lemma resR_one (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U) :
    resR R f (1 : ToType (R.obj.obj (op U))) = 1 :=
  map_one (R.obj.map f.op).hom

/-- Restriction in the sheaf of rings sends zero to zero. -/
lemma resR_zero (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U) :
    resR R f (0 : ToType (R.obj.obj (op U))) = 0 :=
  map_zero (R.obj.map f.op).hom

/-- Restriction in the sheaf of rings commutes with finite sums. -/
lemma resR_sum (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U) {ι : Type*} (t : Finset ι)
    (a : ι → ToType (R.obj.obj (op U))) :
    resR R f (∑ i ∈ t, a i) = ∑ i ∈ t, resR R f (a i) :=
  map_sum (R.obj.map f.op).hom a t

/-- Restricting in the sheaf of rings along `f` and then along `g` is restricting along
`g ≫ f`. -/
lemma resR_resR (R : Sheaf J RingCat.{u}) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (a : ToType (R.obj.obj (op U))) : resR R g (resR R f a) = resR R (g ≫ f) a :=
  (congrFun (congrArg (fun h => (ConcreteCategory.hom h : _ → _))
    (R.obj.map_comp f.op g.op)) a).symm

/-- Restriction of a section of the structure sheaf to an object of the slice site over `U`. -/
noncomputable def resROver (R : Sheaf J RingCat.{u}) {U : C} (V : Over U)
    (a : ToType (R.obj.obj (op U))) : ToType ((R.over U).obj.obj (op V)) :=
  R.obj.map V.hom.op a

/-- A section of `M` over `U`, read as a global section of the restriction `M.over U`. -/
noncomputable def overSection (M : SheafOfModules.{u} R) {U : C}
    (m : ToType (M.val.obj (op U))) : (M.over U).sections :=
  PresheafOfModules.sectionsMk (fun V => M.val.map (V.unop.hom).op m) (by
    intro V W f
    change M.val.map f.unop.left.op (M.val.map (V.unop.hom).op m) = _
    rw [← M.val.map_comp_apply]
    exact M.val.congr_map_apply (congrArg Quiver.Hom.op (Over.w f.unop)) m)

/-- The value of `overSection M m` over `V : Over U` is the restriction of `m` along
`V.hom`. -/
lemma overSection_val (M : SheafOfModules.{u} R) {U : C}
    (m : ToType (M.val.obj (op U))) (V : Over U) :
    (overSection M m).eval (op V) = res M V.hom m := rfl

/-- A global section of a restriction `M.over U` is determined by its value over `U`. -/
lemma overSection_eval_eq (M : SheafOfModules.{u} R) {U : C} (t : (M.over U).sections) :
    overSection M (t.eval (op (Over.mk (𝟙 U)))) = t :=
  PresheafOfModules.sections_ext _ _ fun V =>
    t.property (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op

/-- The morphism from the free sheaf of modules on `ι` to the restriction `M.over U`
determined by a family of sections of `M` over `U`. -/
noncomputable def freeToOver (M : SheafOfModules.{u} R) {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u}
    (s : ι → ToType (M.val.obj (op U))) : free (R := R.over U) ι ⟶ M.over U :=
  (freeHomEquiv _).symm fun i => overSection M (s i)

/-- `freeToOver M s` sends the section with coordinates `c` to the combination
`∑ i, c i • s i` restricted to `V`. -/
lemma freeToOver_app_freeMk (M : SheafOfModules.{u} R) {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) (V : (Over U)ᵒᵖ)
    (c : ι → ToType ((R.over U).obj.obj V)) :
    (freeToOver M s).val.app V (freeMk V c)
      = ∑ i : ι, c i • (overSection M (s i)).eval V := by
  rw [app_freeMk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [freeToOver, ιFree_comp_freeHomEquiv_symm, unitHomEquiv_symm_app_unitOne]

/-- Every morphism `free ι ⟶ M.over U` is `freeToOver M` of the values over `U` of the
corresponding global sections. -/
lemma freeHomEquiv_symm_eq_freeToOver (M : SheafOfModules.{u} R) {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u}
    (t : ι → (M.over U).sections) :
    (freeHomEquiv (M.over U)).symm t
      = freeToOver M (U := U) (fun i => (t i).eval (op (Over.mk (𝟙 U)))) :=
  congrArg _ (funext fun i => (overSection_eval_eq M (t i)).symm)

/-! #### Coordinates over an object of the slice site

`ofCoordsOver` and `coordsOver` repackage `freeMk` and `freeCoord` so that the coordinates live
in `R(V.left)` for an object `V` of the slice site rather than in the structure sheaf of that
site. This is the layer that crosses the transparency boundary described above; it is crossed
exactly in the two defining equations and in the two formulas that evaluate a morphism on such a
section, each of which is proved by `:=` or `exact`. -/

/-- The section of `free ι` over an object `V` of the slice site at `U` with prescribed
coordinates in `R(V.left)`. -/
noncomputable def ofCoordsOver {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [Fintype ι] (V : Over U)
    (c : ι → ToType (R.obj.obj (op V.left))) :
    ToType ((free (R := R.over U) ι).val.obj (op V)) :=
  freeMk (op V) c

/-- The coordinates in `R(V.left)` of a section of `free ι` over an object `V` of the slice site
at `U`. -/
noncomputable def coordsOver {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] (V : Over U)
    (e : ToType ((free (R := R.over U) ι).val.obj (op V))) (i : ι) :
    ToType (R.obj.obj (op V.left)) :=
  freeCoord (op V) e i

/-- The coordinates of `ofCoordsOver V c` are `c`. -/
lemma coordsOver_ofCoordsOver {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] [Fintype ι] (V : Over U) (c : ι → ToType (R.obj.obj (op V.left))) :
    coordsOver V (ofCoordsOver V c) = c :=
  freeCoord_freeMk _ _

/-- A section of `free ι` over `V` is `ofCoordsOver` of its own coordinates. -/
lemma ofCoordsOver_coordsOver {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] [Fintype ι] (V : Over U)
    (e : ToType ((free (R := R.over U) ι).val.obj (op V))) :
    ofCoordsOver V (coordsOver V e) = e :=
  freeMk_freeCoord _ _

/-- Taking coordinates in the base is a bijection between the sections of `free ι` over an
object of the slice site and the tuples of sections of `R` over its source. -/
lemma coordsOver_bijective {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] [Finite ι] (V : Over U) :
    Function.Bijective (coordsOver (R := R) (ι := ι) V) := by
  cases nonempty_fintype ι
  exact Function.bijective_iff_has_inverse.2
    ⟨ofCoordsOver V, ofCoordsOver_coordsOver V, coordsOver_ofCoordsOver V⟩

/-- Coordinates in the base are compatible with the restriction maps of `free ι`. -/
lemma coordsOver_map {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] {V W : Over U} (g : W ⟶ V)
    (e : ToType ((free (R := R.over U) ι).val.obj (op V))) (i : ι) :
    coordsOver W ((free (R := R.over U) ι).val.map g.op e) i
      = resR R g.left (coordsOver V e i) :=
  freeCoord_map g.op e i

/-- Taking coordinates in the base is additive. -/
lemma coordsOver_add {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] (V : Over U)
    (e e' : ToType ((free (R := R.over U) ι).val.obj (op V))) (i : ι) :
    coordsOver V (e + e') i = coordsOver V e i + coordsOver V e' i :=
  (freeProj (S := R.over U) i).val.app (op V) |>.hom.map_add e e'

/-- `freeToOver M s` sends `ofCoordsOver V c` to `∑ i, c i • s i` restricted to `V.left`. -/
lemma freeToOver_app_ofCoordsOver (M : SheafOfModules.{u} R) {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) (V : Over U)
    (c : ι → ToType (R.obj.obj (op V.left))) :
    (freeToOver M s).val.app (op V) (ofCoordsOver V c)
      = ∑ i : ι, c i • res M V.hom (s i) :=
  freeToOver_app_freeMk M s (op V) c

/-! #### Coordinates over a morphism of the site

The same layer indexed by a morphism `f : W ⟶ U` rather than by an object of the slice site.
`Over.mk f` and an arbitrary `V : Over U` with `V.hom = f` are definitionally but not
syntactically equal, so both forms are needed: a statement about sections over `W` wants the
first, and a statement quantified over the slice site wants the second. -/

/-- The section of `free ι` over `f : W ⟶ U` with prescribed coordinates in `R(W)`. -/
noncomputable def ofCoords {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [Fintype ι] {W : C}
    (f : W ⟶ U) (c : ι → ToType (R.obj.obj (op W))) :
    ToType ((free (R := R.over U) ι).val.obj (op (Over.mk f))) :=
  freeMk (op (Over.mk f)) c

/-- The coordinates in `R(W)` of a section of `free ι` over `f : W ⟶ U`. -/
noncomputable def coords {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] {W : C}
    (f : W ⟶ U) (e : ToType ((free (R := R.over U) ι).val.obj (op (Over.mk f)))) (i : ι) :
    ToType (R.obj.obj (op W)) :=
  freeCoord (op (Over.mk f)) e i

/-- The coordinates of `ofCoords f c` are `c`. -/
lemma coords_ofCoords {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] [Fintype ι] {W : C} (f : W ⟶ U)
    (c : ι → ToType (R.obj.obj (op W))) :
    coords f (ofCoords f c) = c :=
  freeCoord_freeMk _ _

/-- A section of `free ι` over `f` is `ofCoords f` of its own coordinates. -/
lemma ofCoords_coords {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] [Fintype ι] {W : C} (f : W ⟶ U)
    (e : ToType ((free (R := R.over U) ι).val.obj (op (Over.mk f)))) :
    ofCoords f (coords f e) = e :=
  freeMk_freeCoord _ _

/-- Coordinates over a morphism are compatible with restriction along `h : W ⟶ V`. -/
lemma coords_map {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {ι : Type u} [DecidableEq ι] {V W : C} (f : V ⟶ U) (h : W ⟶ V)
    (e : ToType ((free (R := R.over U) ι).val.obj (op (Over.mk f)))) (i : ι) :
    coords (h ≫ f) ((free (R := R.over U) ι).val.map
        (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op e) i = resR R h (coords f e i) :=
  freeCoord_map _ e i

/-- `freeToOver M s` sends `ofCoords f c` to `∑ i, c i • s i` restricted along `f`. -/
lemma freeToOver_app_ofCoords (M : SheafOfModules.{u} R) {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) {V : C} (f : V ⟶ U)
    (c : ι → ToType (R.obj.obj (op V))) :
    (freeToOver M s).val.app (op (Over.mk f)) (ofCoords f c)
      = ∑ i : ι, c i • res M f (s i) :=
  freeToOver_app_freeMk M s (op (Over.mk f)) c

end Slice

/-! ### Restricting a sheaf of modules on a space to an open subset -/

section Opens

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- Any two morphisms in the slice category over an open `U` are equal. -/
instance subsingleton_over_hom (U : Opens X) (V W : Over U) : Subsingleton (V ⟶ W) :=
  ⟨fun _ _ => by ext : 1; subsingleton⟩

/-- Any two morphisms in the opposite of the slice category over an open `U` are equal. -/
instance subsingleton_over_op_hom (U : Opens X) (V W : (Over U)ᵒᵖ) : Subsingleton (V ⟶ W) :=
  ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-- Any two morphisms in `(Opens X)ᵒᵖ` are equal. -/
instance subsingleton_opens_op_hom (V W : (Opens X)ᵒᵖ) : Subsingleton (V ⟶ W) :=
  ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-! ### Local presentation data at a point -/

/-- Section-level finite presentation data for a sheaf of modules on a neighbourhood of a
point: finitely many generating sections `u`, and a finite family `rel` of relations between
them which generates all relations locally. -/
@[ega "0 5.2.5" "local clause at a point"]
structure LocalPresentation (M : SheafOfModules.{u} R) (x : X) where
  /-- the neighbourhood on which the presentation lives -/
  nhd : Opens X
  /-- the neighbourhood contains the point -/
  mem_nhd : x ∈ nhd
  /-- index type of the generators -/
  Gen : Type u
  /-- index type of the relations -/
  Rel : Type u
  /-- there are finitely many generators -/
  fintypeGen : Fintype Gen
  /-- there are finitely many relations -/
  fintypeRel : Fintype Rel
  /-- the generating sections -/
  gens : Gen → ToType (M.val.obj (op nhd))
  /-- the relations, as a `Rel`-indexed family of `Gen`-tuples of sections of the structure
  sheaf -/
  rel : Rel → Gen → ToType (R.obj.obj (op nhd))
  /-- each relation is indeed a relation between the generators -/
  rel_apply : ∀ l, ∑ k : Gen, rel l k • gens k = 0
  /-- the generators generate locally -/
  generates : ∀ ⦃V : Opens X⦄ (f : V ⟶ nhd) (t : ToType (M.val.obj (op V))) (y : X), y ∈ V →
    ∃ (W : Opens X) (g : W ⟶ V), y ∈ W ∧ ∃ c : Gen → ToType (R.obj.obj (op W)),
      res M g t = ∑ k : Gen, c k • res M (g ≫ f) (gens k)
  /-- the relations generate all relations locally -/
  relations : ∀ ⦃V : Opens X⦄ (f : V ⟶ nhd) (z : Gen → ToType (R.obj.obj (op V))),
    (∑ k : Gen, z k • res M f (gens k) = 0) → ∀ y ∈ V,
    ∃ (W : Opens X) (g : W ⟶ V), y ∈ W ∧ ∃ b : Rel → ToType (R.obj.obj (op W)),
      ∀ k : Gen, resR R g (z k) = ∑ l : Rel, b l * resR R (g ≫ f) (rel l k)

attribute [instance] LocalPresentation.fintypeGen LocalPresentation.fintypeRel


/-! ### Extracting local presentation data from finite presentation -/

/-- Sections of the target of an epimorphism of sheaves of modules over the slice site at an
open `U` lie in the image after restricting to a small enough neighbourhood of any point. -/
lemma exists_nbhd_mem_range_of_epi {U : Opens X} {N P : SheafOfModules.{u} (R.over U)}
    (f : N ⟶ P) [Epi f] (V : Over U) (t : ToType (P.val.obj (op V))) (y : X) (hy : y ∈ V.left) :
    ∃ (W : Opens X) (h : W ⟶ V.left), y ∈ W ∧
      ∃ z, f.val.app (op (Over.mk (h ≫ V.hom))) z
        = P.val.map (Over.homMk h : Over.mk (h ≫ V.hom) ⟶ V).op t := by
  have hS := EpiMono.imageSieve_mem_of_epi f t
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology] at hS
  obtain ⟨W, h, hmem, hyW⟩ := hS y hy
  rw [Sieve.overEquiv_iff] at hmem
  exact ⟨W, h, hyW, hmem⟩

/-- Variant of `exists_nbhd_mem_range_of_epi` indexed by an inclusion of opens. -/
lemma exists_nbhd_mem_range_of_epi' {U : Opens X} {N P : SheafOfModules.{u} (R.over U)}
    (φ : N ⟶ P) [Epi φ] {V : Opens X} (f : V ⟶ U)
    (t : ToType (P.val.obj (op (Over.mk f)))) (y : X) (hy : y ∈ V) :
    ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧
      ∃ z, φ.val.app (op (Over.mk (h ≫ f))) z
        = P.val.map (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op t :=
  exists_nbhd_mem_range_of_epi φ (Over.mk f) t y hy

/-- The matrix of a morphism between finite free sheaves of modules over the slice site at an
open `U`: its `(l, k)` entry is the `k`-th coordinate over `U` of the image of the `l`-th
basis section. -/
noncomputable def freeMat {U : Opens X} {Rel Gen : Type u} [DecidableEq Gen]
    (χ : free (R := R.over U) Rel ⟶ free (R := R.over U) Gen) (l : Rel) (k : Gen) :
    ToType (R.obj.obj (op U)) :=
  coords (R := R) (𝟙 U) ((ιFree l ≫ χ).val.app (op (Over.mk (𝟙 U))) (unitOne _)) k

/-- The image of the unit section under a morphism out of `unit` is compatible with
restriction. -/
lemma app_unitOne_eq_map {U : Opens X} {N : SheafOfModules.{u} (R.over U)}
    (a : unit (R.over U) ⟶ N) {V W : (Over U)ᵒᵖ} (m : V ⟶ W) :
    a.val.app W (unitOne W) = N.val.map m (a.val.app V (unitOne V)) := by
  have h := PresheafOfModules.naturality_apply a.val m (unitOne (S := R.over U) V)
  rwa [show (unit (R.over U)).val.map m (unitOne (S := R.over U) V)
    = unitOne (S := R.over U) W from PresheafOfModules.unit_map_one _ m] at h

/-- The image over `V` of the unit section under a morphism `unit ⟶ free ι` has as
coordinates the restrictions to `V` of the coordinates of its image over `U`. -/
lemma app_unitOne_eq_freeMk {U : Opens X} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : unit (R.over U) ⟶ free (R := R.over U) ι) (V : Over U) :
    a.val.app (op V) (unitOne _)
      = freeMk (op V) (fun k => resROver R V
          (freeCoord (op (Over.mk (𝟙 U))) (a.val.app (op (Over.mk (𝟙 U))) (unitOne _)) k)) := by
  rw [← freeMk_freeCoord (S := R.over U) (ι := ι) (op V) (a.val.app (op V) (unitOne _))]
  refine congrArg _ (funext fun k => ?_)
  rw [app_unitOne_eq_map a (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op, freeCoord_map]
  rfl

/-- The coordinate description, over the slice site, of the action of a morphism between finite
free sheaves of modules on sections. -/
lemma freeCoord_app_freeMk {U : Opens X} {Rel Gen : Type u} [Fintype Rel] [Finite Gen]
    [DecidableEq Gen] (χ : free (R := R.over U) Rel ⟶ free (R := R.over U) Gen) (V : Over U)
    (c : Rel → ToType ((R.over U).obj.obj (op V))) (k : Gen) :
    freeCoord (op V) (χ.val.app (op V) (freeMk (op V) c)) k
      = ∑ l : Rel, c l * resROver R V (freeMat χ l k) := by
  cases nonempty_fintype Gen
  rw [app_freeMk, show (∑ l : Rel, c l • (ιFree l ≫ χ).val.app (op V)
        (unitOne (S := R.over U) (op V)))
      = ∑ l : Rel, freeMk (op V) (fun k' => c l * resROver R V (freeMat χ l k')) from
    Finset.sum_congr rfl fun l _ => by
      rw [app_unitOne_eq_freeMk (ιFree l ≫ χ) V, freeMk_smul]
      rfl, freeMk_sum, freeCoord_freeMk]

/-- The coordinate description, over an open subset, of the action of a morphism between finite
free sheaves of modules on sections. -/
lemma coords_app_ofCoords {U : Opens X} {Rel Gen : Type u} [Fintype Rel] [Finite Gen]
    [DecidableEq Gen] (χ : free (R := R.over U) Rel ⟶ free (R := R.over U) Gen) {V : Opens X}
    (f : V ⟶ U) (c : Rel → ToType (R.obj.obj (op V))) (k : Gen) :
    coords f (χ.val.app (op (Over.mk f)) (ofCoords f c)) k
      = ∑ l : Rel, c l * resR R f (freeMat χ l k) :=
  freeCoord_app_freeMk χ (Over.mk f) c k

/-- If a morphism out of a finite free sheaf of modules composes to zero with `g`, then the
sections of the target given by the rows of its matrix are killed by `g`. -/
lemma app_ofCoords_freeMat {U : Opens X} {Rel Gen : Type u} [Fintype Gen] [DecidableEq Gen]
    {N : SheafOfModules.{u} (R.over U)}
    (χ : free (R := R.over U) Rel ⟶ free (R := R.over U) Gen)
    (g : free (R := R.over U) Gen ⟶ N) (hχ : χ ≫ g = 0) (l : Rel) :
    g.val.app (op (Over.mk (𝟙 U))) (ofCoords (𝟙 U) (freeMat χ l)) = 0 := by
  rw [show ofCoords (𝟙 U) (freeMat χ l)
      = (ιFree l ≫ χ).val.app (op (Over.mk (𝟙 U)))
          (unitOne (S := R.over U) (op (Over.mk (𝟙 U)))) from
    ofCoords_coords (ι := Gen) (𝟙 U) _,
    show g.val.app (op (Over.mk (𝟙 U))) ((ιFree l ≫ χ).val.app (op (Over.mk (𝟙 U)))
        (unitOne (S := R.over U) (op (Over.mk (𝟙 U)))))
      = ((ιFree l ≫ χ) ≫ g).val.app (op (Over.mk (𝟙 U)))
          (unitOne (S := R.over U) (op (Over.mk (𝟙 U)))) from rfl,
    show (ιFree l ≫ χ) ≫ g = 0 from by rw [Category.assoc, hχ, comp_zero]]
  exact zero_app_apply _ _

/-- If the morphism from the free sheaf of modules determined by finitely many sections is an
epimorphism, then those sections generate `M` locally at every point. -/
lemma generates_of_epi (M : SheafOfModules.{u} R) {U : Opens X} {ι : Type u} [Fintype ι]
    (u : ι → ToType (M.val.obj (op U))) [Epi (freeToOver M u)]
    ⦃V : Opens X⦄ (f : V ⟶ U) (t : ToType (M.val.obj (op V))) (y : X) (hy : y ∈ V) :
    ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ ∃ c : ι → ToType (R.obj.obj (op W)),
      res M h t = ∑ k : ι, c k • res M (h ≫ f) (u k) := by
  classical
  obtain ⟨W, h, hyW, z, hz⟩ := exists_nbhd_mem_range_of_epi' (freeToOver M u) f t y hy
  refine ⟨W, h, hyW, coords (R := R) (h ≫ f) z, ?_⟩
  refine Eq.symm (Eq.trans (Eq.trans
    (freeToOver_app_ofCoords M u (h ≫ f) (coords (R := R) (ι := ι) (h ≫ f) z)).symm
    (congrArg (fun e => (freeToOver M u).val.app (op (Over.mk (h ≫ f))) e)
      (ofCoords_coords (h ≫ f) z))) hz)

/-- A tuple of sections of the structure sheaf over `V ≤ U` whose associated section of the
free sheaf on `Gen` is killed by `g` is, near every point, a combination of the rows of the
matrix of `κ ≫ kernel.ι g`. This is the local-exactness statement extracted from a
presentation. -/
lemma exists_nbhd_coords_eq {U : Opens X} {Rel Gen : Type u} [Fintype Rel] [Fintype Gen]
    [DecidableEq Gen] {N : SheafOfModules.{u} (R.over U)}
    (g : free (R := R.over U) Gen ⟶ N) (κ : free (R := R.over U) Rel ⟶ kernel g) [Epi κ]
    {V : Opens X} (f : V ⟶ U) (z : Gen → ToType (R.obj.obj (op V)))
    (hζ : g.val.app (op (Over.mk f)) (ofCoords f z) = 0) (y : X) (hy : y ∈ V) :
    ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ ∃ b : Rel → ToType (R.obj.obj (op W)),
      ∀ k : Gen, resR R h (z k)
        = ∑ l : Rel, b l * resR R (h ≫ f) (freeMat (κ ≫ kernel.ι g) l k) := by
  classical
  obtain ⟨w, hw⟩ := exists_kernel_section g (op (Over.mk f)) (ofCoords f z) hζ
  obtain ⟨W, h, hyW, b, hb⟩ := exists_nbhd_mem_range_of_epi' κ f w y hy
  refine ⟨W, h, hyW, coords (R := R) (h ≫ f) b, fun k => ?_⟩
  have e1 : (κ ≫ kernel.ι g).val.app (op (Over.mk (h ≫ f))) b
      = (kernel.ι g).val.app (op (Over.mk (h ≫ f)))
          (κ.val.app (op (Over.mk (h ≫ f))) b) := rfl
  have e2 := congrArg (fun e => (kernel.ι g).val.app (op (Over.mk (h ≫ f))) e) hb
  have e3 := PresheafOfModules.naturality_apply (kernel.ι g).val
    (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op w
  have e4 := congrArg (fun e => (free (R := R.over U) Gen).val.map
    (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op e) hw
  have hcoord := congrArg (fun e => coords (ι := Gen) (h ≫ f) e k)
    (e1.trans (e2.trans (e3.trans e4)))
  have hA := (congrArg (fun e => coords (R := R) (ι := Gen) (h ≫ f)
      ((κ ≫ kernel.ι g).val.app (op (Over.mk (h ≫ f))) e) k)
    (ofCoords_coords (h ≫ f) b)).symm.trans
      (coords_app_ofCoords (κ ≫ kernel.ι g) (h ≫ f) (coords (R := R) (ι := Rel) (h ≫ f) b) k)
  have hR : coords (ι := Gen) (h ≫ f)
        ((free (R := R.over U) Gen).val.map
          (Over.homMk h : Over.mk (h ≫ f) ⟶ Over.mk f).op (ofCoords f z)) k
      = resR R h (z k) :=
    (coords_map (R := R) f h (ofCoords f z) k).trans
      (congrArg (fun c : Gen → ToType (R.obj.obj (op V)) => resR R h (c k))
        (coords_ofCoords f z))
  exact hR.symm.trans (hcoord.symm.trans hA)

section Presentation

variable (M : SheafOfModules.{u} R) {U : Opens X} (P : (M.over U).Presentation)

/-- The generating sections of a presentation of `M.over U`, read as sections of `M` over `U`. -/
noncomputable def presGens (k : P.generators.I) : ToType (M.val.obj (op U)) :=
  (P.generators.s k).eval (op (Over.mk (𝟙 U)))

/-- The relation matrix of a presentation of `M.over U`. -/
noncomputable def presRel [DecidableEq P.generators.I] (l : P.relations.I)
    (k : P.generators.I) : ToType (R.obj.obj (op U)) :=
  freeMat (P.relations.π ≫ kernel.ι P.generators.π) l k

/-- The generating morphism of the presentation is `freeToOver M` of its generating
sections. -/
lemma presGens_π : P.generators.π = freeToOver M (presGens M P) :=
  freeHomEquiv_symm_eq_freeToOver M _

/-- The morphism determined by the generating sections of a presentation is an
epimorphism. -/
lemma epi_freeToOver_presGens : Epi (freeToOver M (presGens M P)) := by
  rw [← presGens_π]; exact P.generators.epi

/-- The generating morphism sends `ofCoords f c` to the combination of the restricted
generating sections with coefficients `c`. -/
lemma presGens_app [Fintype P.generators.I] {V : Opens X} (f : V ⟶ U)
    (c : P.generators.I → ToType (R.obj.obj (op V))) :
    P.generators.π.val.app (op (Over.mk f)) (ofCoords f c)
      = ∑ k : P.generators.I, c k • res M f (presGens M P k) := by
  rw [presGens_π]
  exact freeToOver_app_ofCoords M _ f c

/-- Each row of the relation matrix is a relation between the generating sections. -/
lemma presRel_apply [Fintype P.generators.I] [DecidableEq P.generators.I]
    (l : P.relations.I) : ∑ k : P.generators.I, presRel M P l k • presGens M P k = 0 := by
  have hc : (P.relations.π ≫ kernel.ι P.generators.π) ≫ P.generators.π = 0 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => P.relations.π ≫ g) (kernel.condition P.generators.π)).trans comp_zero)
  have h0 := app_ofCoords_freeMat (P.relations.π ≫ kernel.ι P.generators.π) P.generators.π hc l
  rw [presGens_app] at h0
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
  rw [res_id]
  rfl

/-- Every relation between the restricted generating sections is, near every point, a
combination of the rows of the relation matrix. -/
lemma presRel_relations [Fintype P.generators.I] [Fintype P.relations.I]
    [DecidableEq P.generators.I] ⦃V : Opens X⦄ (f : V ⟶ U)
    (z : P.generators.I → ToType (R.obj.obj (op V)))
    (hz : ∑ k : P.generators.I, z k • res M f (presGens M P k) = 0) (y : X) (hy : y ∈ V) :
    ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧
      ∃ b : P.relations.I → ToType (R.obj.obj (op W)),
        ∀ k : P.generators.I, resR R h (z k)
          = ∑ l : P.relations.I, b l * resR R (h ≫ f) (presRel M P l k) := by
  classical
  have hζ : P.generators.π.val.app (op (Over.mk f)) (ofCoords f z) = 0 := by
    rw [presGens_app]; exact hz
  exact exists_nbhd_coords_eq P.generators.π P.relations.π f z hζ y hy

/-- Section-level presentation data extracted from a finite presentation of `M.over U`. -/
noncomputable def localPresentationOfPresentation [P.IsFinite] {x : X} (hx : x ∈ U) :
    LocalPresentation M x := by
  classical
  haveI : Fintype P.generators.I := Fintype.ofFinite _
  haveI : Fintype P.relations.I := Fintype.ofFinite _
  have := epi_freeToOver_presGens M P
  exact
    { nhd := U
      mem_nhd := hx
      Gen := P.generators.I
      Rel := P.relations.I
      fintypeGen := inferInstance
      fintypeRel := inferInstance
      gens := presGens M P
      rel := presRel M P
      rel_apply := presRel_apply M P
      generates := generates_of_epi M (presGens M P)
      relations := presRel_relations M P }

end Presentation

/-- **Stacks Project, Tag 01BN** in concrete form: a finitely presented sheaf of modules admits
section-level presentation data on a neighbourhood of every point. -/
theorem nonempty_localPresentation (M : SheafOfModules.{u} R) [M.IsFinitePresentation] (x : X) :
    Nonempty (LocalPresentation M x) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨i₀, hi₀⟩ : ∃ i, x ∈ q.X i := by
    have h : IsOpenCover q.X := (Opens.coversTop_iff (X : Type u) q.X).1 q.coversTop
    have hx : x ∈ (⨆ i, q.X i) := by rw [h.iSup_eq_top]; exact Opens.mem_top x
    simpa using hx
  have := hq.isFinite_presentation i₀
  exact ⟨localPresentationOfPresentation M (q.presentation i₀) hi₀⟩



/-! ### Germs of sections -/

section Germs

variable (M : SheafOfModules.{u} R) (x : X)

/-- The germ at `x` of a section of `M` over an open neighbourhood of `x`. -/
noncomputable def germ {U : Opens X} (hx : x ∈ U) (m : ToType (M.val.obj (op U))) :
    ToType (TopCat.Presheaf.stalk M.val.presheaf x) :=
  TopCat.Presheaf.germ M.val.presheaf U x hx m

variable {M}

/-- The germ of `a • m` is the germ of `a` times the germ of `m`. -/
lemma germ_smul {U : Opens X} (hx : x ∈ U) (a : ToType (R.obj.obj (op U)))
    (m : ToType (M.val.obj (op U))) :
    germ M x hx (a • m)
      = TopCat.Presheaf.germ R.obj U x hx a • germ M x hx m :=
  PresheafOfModules.germ_ringCat_smul M.val x U hx a m

/-- Taking germs commutes with finite sums. -/
lemma germ_sum {U : Opens X} (hx : x ∈ U) {ι : Type*} (t : Finset ι)
    (m : ι → ToType (M.val.obj (op U))) :
    germ M x hx (∑ i ∈ t, m i) = ∑ i ∈ t, germ M x hx (m i) :=
  map_sum (TopCat.Presheaf.germ M.val.presheaf U x hx).hom m t

/-- The germ of zero is zero. -/
lemma germ_zero {U : Opens X} (hx : x ∈ U) :
    germ M x hx (0 : ToType (M.val.obj (op U))) = 0 :=
  map_zero (TopCat.Presheaf.germ M.val.presheaf U x hx).hom

/-- The germ of a restriction is the germ of the original section. -/
lemma germ_res {U V : Opens X} (h : V ⟶ U) (hx : x ∈ V) (m : ToType (M.val.obj (op U))) :
    germ M x hx (res M h m) = germ M x (h.le hx) m :=
  TopCat.Presheaf.germ_res_apply M.val.presheaf h x hx m

/-- Two sections with the same germ at `x` agree on a neighbourhood of `x`. -/
lemma exists_res_eq {U : Opens X} (hx : x ∈ U) (m m' : ToType (M.val.obj (op U)))
    (hmm : germ M x hx m = germ M x hx m') :
    ∃ (W : Opens X) (h : W ⟶ U), x ∈ W ∧ res M h m = res M h m' := by
  obtain ⟨W, hxW, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq M.val.presheaf x hx hx m m' hmm
  refine ⟨W, i₁, hxW, ?_⟩
  rw [show res M i₁ m = M.val.presheaf.map i₁.op m from rfl, he,
    Subsingleton.elim i₂ i₁]
  rfl

/-- Finitely many neighbourhoods of a point have a common refinement which is again a
neighbourhood. -/
lemma exists_nbhd_le {ι : Type*} [Finite ι] (W : ι → Opens X) (hW : ∀ i, x ∈ W i) :
    ∃ V : Opens X, x ∈ V ∧ ∀ i, V ≤ W i := by
  classical
  cases nonempty_fintype ι
  refine ⟨Finset.univ.inf W, ?_, fun i => Finset.inf_le (Finset.mem_univ i)⟩
  have key : ∀ t : Finset ι, x ∈ t.inf W := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hW a, ih⟩
  exact key _

end Germs


/-! ### Trivialisation from injectivity plus local surjectivity -/

section Trivialise

variable (M : SheafOfModules.{u} R) {U : Opens X} {ι : Type u} [Fintype ι]
  (s : ι → ToType (M.val.obj (op U)))

/-- The map on sections of `freeToOver M s` in coordinates. -/
lemma freeToOver_app_eq_sum [DecidableEq ι] (V : (Over U)ᵒᵖ)
    (e : ToType ((free (R := R.over U) ι).val.obj V)) :
    (freeToOver M s).val.app V e
      = ∑ i : ι, freeCoord (S := R.over U) V e i • (overSection M (s i)).eval V := by
  conv_lhs => rw [← freeMk_freeCoord (S := R.over U) (ι := ι) V e]
  exact freeToOver_app_freeMk M s V _

/-- If taking `R(V)`-combinations of the sections `s` is injective over every open `V ≤ U`,
then the induced morphism from the free sheaf of modules is a monomorphism. -/
lemma mono_freeToOver
    (hinj : ∀ ⦃V : Opens X⦄ (f : V ⟶ U), Function.Injective
      (fun c : ι → ToType (R.obj.obj (op V)) => ∑ i : ι, c i • res M f (s i))) :
    Mono (freeToOver M s) := by
  classical
  refine (SheafOfModules.forget (R.over U)).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun V e e' hee => ?_)
  refine (freeCoord_bijective (S := R.over U) (ι := ι) V).1 (hinj V.unop.hom ?_)
  exact (freeToOver_app_eq_sum M s V e).symm.trans
    (hee.trans (freeToOver_app_eq_sum M s V e'))

/-- If every section of `M` over an open `V ≤ U` is, near every point of `V`, an
`R`-combination of the sections `s`, then the induced morphism from the free sheaf of modules
is an epimorphism. -/
lemma epi_freeToOver
    (hsurj : ∀ ⦃V : Opens X⦄ (f : V ⟶ U) (t : ToType (M.val.obj (op V))) (y : X), y ∈ V →
      ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ ∃ c : ι → ToType (R.obj.obj (op W)),
        res M h t = ∑ i : ι, c i • res M (h ≫ f) (s i)) :
    Epi (freeToOver M s) := by
  classical
  refine EpiMono.epi_of_isLocallySurjective (freeToOver M s) ⟨fun {V} t => ?_⟩
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro y hy
  obtain ⟨W, h, hyW, c, hc⟩ := hsurj V.hom t y hy
  refine ⟨W, h, ?_, hyW⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨ofCoords (h ≫ V.hom) c,
    (freeToOver_app_ofCoords M s (h ≫ V.hom) c).trans hc.symm⟩

/-- `M` is isomorphic to the free sheaf of modules on `U` as soon as taking combinations of
the sections `s` is injective over every open `V ≤ U` and locally surjective. -/
theorem nonempty_over_iso_free_of_inj_of_surj
    (hinj : ∀ ⦃V : Opens X⦄ (f : V ⟶ U), Function.Injective
      (fun c : ι → ToType (R.obj.obj (op V)) => ∑ i : ι, c i • res M f (s i)))
    (hsurj : ∀ ⦃V : Opens X⦄ (f : V ⟶ U) (t : ToType (M.val.obj (op V))) (y : X), y ∈ V →
      ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ ∃ c : ι → ToType (R.obj.obj (op W)),
        res M h t = ∑ i : ι, c i • res M (h ≫ f) (s i)) :
    Nonempty (M.over U ≅ free (R := R.over U) ι) :=
  have _ := mono_freeToOver M s hinj
  have _ := epi_freeToOver M s hsurj
  have _ : IsIso (freeToOver M s) := isIso_of_mono_of_epi _
  ⟨(asIso (freeToOver M s)).symm⟩

end Trivialise


/-! ### Spreading a free stalk to a neighbourhood -/

section StalkFree

/-- The restriction of a linear combination is the combination of the restrictions with
restricted coefficients. -/
lemma res_sum_smul (M : SheafOfModules.{u} R) {U V : Opens X} (f : V ⟶ U) {ι : Type*}
    (t : Finset ι) (c : ι → ToType (R.obj.obj (op U))) (m : ι → ToType (M.val.obj (op U))) :
    res M f (∑ i ∈ t, c i • m i) = ∑ i ∈ t, resR R f (c i) • res M f (m i) := by
  rw [res_sum]
  exact Finset.sum_congr rfl fun i _ => res_smul M f (c i) (m i)

/-- The germ of a restricted section of the sheaf of rings is the germ of the original
section. -/
lemma germR_res (x : X) {U V : Opens X} (h : V ⟶ U) (hx : x ∈ V)
    (a : ToType (R.obj.obj (op U))) :
    TopCat.Presheaf.germ R.obj V x hx (resR R h a)
      = TopCat.Presheaf.germ R.obj U x (h.le hx) a :=
  TopCat.Presheaf.germ_res_apply R.obj h x hx a

/-- A section of the sheaf of rings whose germ at `x` vanishes vanishes near `x`. -/
lemma exists_resR_eq_zero (x : X) {U : Opens X} (hx : x ∈ U)
    (a : ToType (R.obj.obj (op U))) (ha : TopCat.Presheaf.germ R.obj U x hx a = 0) :
    ∃ (W : Opens X) (h : W ⟶ U), x ∈ W ∧ resR R h a = 0 := by
  obtain ⟨W, hxW, i₁, i₂, he⟩ :=
    TopCat.Presheaf.germ_eq R.obj x hx hx a 0 (ha.trans (map_zero _).symm)
  exact ⟨W, i₁, hxW, he.trans (map_zero _)⟩

/-- A section of the sheaf of rings which vanishes near every point vanishes. -/
lemma eq_zero_of_locally_zero {V : Opens X} (a : ToType (R.obj.obj (op V)))
    (ha : ∀ y ∈ V, ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ resR R h a = 0) : a = 0 := by
  refine TopCat.Presheaf.section_ext R V a 0 fun y hy => ?_
  obtain ⟨W, h, hyW, h0⟩ := ha y hy
  calc TopCat.Presheaf.germ R.obj V y hy a
      = TopCat.Presheaf.germ R.obj W y hyW (resR R h a) :=
        (TopCat.Presheaf.germ_res_apply R.obj h y hyW a).symm
    _ = 0 := by rw [h0]; exact map_zero _
    _ = TopCat.Presheaf.germ R.obj V y hy 0 := (map_zero _).symm

/-- Finitely many neighbourhoods of a point, together with a fixed one, have a common
refinement which is again a neighbourhood. -/
lemma exists_nbhd_le' (x : X) (U : Opens X) (hxU : x ∈ U) {ι : Type*} [Finite ι]
    (W : ι → Opens X) (hW : ∀ i, x ∈ W i) :
    ∃ (V : Opens X) (_ : V ⟶ U), x ∈ V ∧ ∀ i, V ≤ W i := by
  obtain ⟨V, hxV, hle⟩ := exists_nbhd_le x (fun o : Option ι => o.elim U W)
    (by rintro (_ | i) <;> [exact hxU; exact hW i])
  exact ⟨V, homOfLE (hle none), hxV, fun i => hle (some i)⟩

/-- Sections whose germs realise a given basis of the stalk. -/
lemma exists_sections_germ_eq (M : SheafOfModules.{u} R) (x : X) {ρ : Type u} [Finite ρ]
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) (U₀ : Opens X) (hxU₀ : x ∈ U₀) :
    ∃ (U : Opens X) (_ : U ⟶ U₀) (hx : x ∈ U) (s : ρ → ToType (M.val.obj (op U))),
      ∀ i, germ M x hx (s i) = bas i := by
  choose V hV m hm using fun i : ρ => TopCat.Presheaf.exists_germ_eq M.val.presheaf (bas i)
  obtain ⟨U, h, hxU, hle⟩ := exists_nbhd_le' x U₀ hxU₀ V hV
  exact ⟨U, h, hxU, fun i => res M (homOfLE (hle i)) (m i), fun i =>
    (germ_res x (homOfLE (hle i)) hxU (m i)).trans (hm i)⟩

/-- A section near `x` is, after shrinking, a combination of sections whose germs form a basis
of the stalk at `x`. -/
lemma exists_res_eq_sum_of_basis (M : SheafOfModules.{u} R) (x : X) {ρ : Type u} [Fintype ρ]
    {U : Opens X} (hxU : x ∈ U) (s : ρ → ToType (M.val.obj (op U)))
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)))
    (hs : ∀ i, germ M x hxU (s i) = bas i)
    (t : ToType (M.val.obj (op U))) :
    ∃ (W : Opens X) (h : W ⟶ U) (_ : x ∈ W) (c : ρ → ToType (R.obj.obj (op W))),
      res M h t = ∑ i : ρ, c i • res M h (s i) := by
  classical
  choose V hV a ha using fun i : ρ =>
    TopCat.Presheaf.exists_germ_eq R.obj (bas.repr (germ M x hxU t) i)
  obtain ⟨W₀, h₀, hxW₀, hle⟩ := exists_nbhd_le' x U hxU V hV
  have hgerm : germ M x hxW₀ (∑ i : ρ, resR R (homOfLE (hle i)) (a i) • res M h₀ (s i))
      = germ M x hxW₀ (res M h₀ t) := by
    rw [germ_sum, germ_res]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (bas.sum_repr (germ M x hxU t))
    rw [germ_smul, germR_res, germ_res, ha i, hs i]
  obtain ⟨W, h, hxW, he⟩ := exists_res_eq x hxW₀ _ _ hgerm
  refine ⟨W, h ≫ h₀, hxW, fun i => resR R h (resR R (homOfLE (hle i)) (a i)), ?_⟩
  rw [← res_res M h₀ h t, ← he, res_sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [res_res]

end StalkFree



/-! ### Finite-sum identities -/

section SumIdentities

variable {Rr : Type*} [Ring Rr] {Mm : Type*} [AddCommGroup Mm] [Module Rr Mm]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Composing a change of generators with a combination. -/
lemma sum_smul_sum_smul (a : ι → Rr) (A : ι → κ → Rr) (m : κ → Mm) :
    ∑ i : ι, a i • (∑ k : κ, A i k • m k) = ∑ k : κ, (∑ i : ι, a i * A i k) • m k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Composing two matrices. -/
lemma sum_mul_sum_mul (a : ι → Rr) (A : ι → κ → Rr) (B : κ → Rr) :
    ∑ k : κ, (∑ i : ι, a i * A i k) * B k = ∑ i : ι, a i * (∑ k : κ, A i k * B k) := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Composing two matrices, the other association. -/
lemma sum_mul_sum_mul' (b : ι → Rr) (A : ι → κ → Rr) (B : κ → Rr) :
    ∑ k : κ, (∑ l : ι, b l * A l k) * B k = ∑ l : ι, b l * (∑ k : κ, A l k * B k) :=
  sum_mul_sum_mul b A B

/-- A combination against a row of the identity matrix. -/
lemma sum_mul_ite [DecidableEq ι] (a : ι → Rr) (i : ι) :
    ∑ i' : ι, a i' * (if i' = i then (1 : Rr) else 0) = a i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun b _ hb => by simp [hb])]
  simp

end SumIdentities


/-! ### The chart -/

section Chart

/-- Restricting a relation `m = ∑ cᵢ • res g (nᵢ)` along `f` restricts the coefficients. -/
private lemma res_eq_sum_smul_res (M : SheafOfModules.{u} R) {U V W : Opens X} (g : V ⟶ U)
    (f : W ⟶ V) {ι : Type*} {t : Finset ι} {c : ι → ToType (R.obj.obj (op V))}
    {n : ι → ToType (M.val.obj (op U))} {m : ToType (M.val.obj (op V))}
    (h : m = ∑ i ∈ t, c i • res M g (n i)) :
    res M f m = ∑ i ∈ t, resR R f (c i) • res M (f ≫ g) (n i) :=
  ((congrArg (res M f) h).trans (res_sum_smul M f t c _)).trans
    (Finset.sum_congr rfl fun i _ => by rw [res_res])

/-- The germ of a linear combination is the combination of the germs. -/
private lemma germ_sum_smul (M : SheafOfModules.{u} R) (x : X) {U : Opens X} (hx : x ∈ U)
    {ι : Type*} (t : Finset ι) (c : ι → ToType (R.obj.obj (op U)))
    (m : ι → ToType (M.val.obj (op U))) :
    germ M x hx (∑ i ∈ t, c i • m i)
      = ∑ i ∈ t, TopCat.Presheaf.germ R.obj U x hx (c i) • germ M x hx (m i) :=
  (germ_sum x hx t _).trans (Finset.sum_congr rfl fun i _ => germ_smul x hx (c i) (m i))

/-- The germ of a sum of products is the sum of the products of the germs. -/
private lemma germR_sum_mul (x : X) {U : Opens X} (hx : x ∈ U) {ι : Type*} (t : Finset ι)
    (a b : ι → ToType (R.obj.obj (op U))) :
    TopCat.Presheaf.germ R.obj U x hx (∑ i ∈ t, a i * b i)
      = ∑ i ∈ t, TopCat.Presheaf.germ R.obj U x hx (a i)
          * TopCat.Presheaf.germ R.obj U x hx (b i) :=
  (map_sum _ _ _).trans (Finset.sum_congr rfl fun _ _ => map_mul _ _ _)

/-- Restriction in the sheaf of rings turns a sum of products into the sum of the restricted
products. -/
private lemma resR_sum_mul {U V : Opens X} (f : V ⟶ U) {ι : Type*} (t : Finset ι)
    (a b : ι → ToType (R.obj.obj (op U))) :
    resR R f (∑ i ∈ t, a i * b i) = ∑ i ∈ t, resR R f (a i) * resR R f (b i) :=
  (resR_sum R f t _).trans (Finset.sum_congr rfl fun _ _ => resR_mul R f _ _)

/-- A section of the sheaf of rings killed by `g` is killed by every `f ≫ g`. -/
private lemma resR_comp_eq_zero {U V W : Opens X} {g : V ⟶ U} {a : ToType (R.obj.obj (op U))}
    (h : resR R g a = 0) (f : W ⟶ V) : resR R (f ≫ g) a = 0 :=
  (resR_resR R g f a).symm.trans ((congrArg (resR R f) h).trans (resR_zero R f))

/-- **Spreading a free stalk.** Near a point `x` at which the stalk of a finitely presented
sheaf of modules is free on a finite basis there are: a section-level presentation of `M`,
sections `s` realising the basis, and matrices `A`, `B` expressing the `s` through the
generators and conversely, subject to the two identities `A * B = 1` and `rel * B = 0`. -/
lemma exists_chart (M : SheafOfModules.{u} R) [M.IsFinitePresentation] (x : X)
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ (LP : LocalPresentation M x) (U : Opens X) (fU : U ⟶ LP.nhd) (_ : x ∈ U)
      (s : ρ → ToType (M.val.obj (op U)))
      (A : ρ → LP.Gen → ToType (R.obj.obj (op U)))
      (B : LP.Gen → ρ → ToType (R.obj.obj (op U))),
      (∀ i, s i = ∑ k : LP.Gen, A i k • res M fU (LP.gens k)) ∧
      (∀ k, res M fU (LP.gens k) = ∑ i : ρ, B k i • s i) ∧
      (∀ i i', ∑ k : LP.Gen, A i k * B k i' = if i = i' then 1 else 0) ∧
      (∀ l i, ∑ k : LP.Gen, resR R fU (LP.rel l k) * B k i = 0) := by
  classical
  obtain ⟨LP⟩ := nonempty_localPresentation M x
  obtain ⟨U₁, g₁, hxU₁, s₁, hs₁⟩ := exists_sections_germ_eq M x bas LP.nhd LP.mem_nhd
  choose Wa ga hxWa A₀ hA₀ using fun i : ρ => LP.generates g₁ (s₁ i) x hxU₁
  obtain ⟨U₂, g₂₁, hxU₂, hle₂⟩ := exists_nbhd_le' x U₁ hxU₁ Wa hxWa
  have hs₂ : ∀ i, germ M x hxU₂ (res M g₂₁ (s₁ i)) = bas i := fun i =>
    (germ_res x g₂₁ hxU₂ (s₁ i)).trans (hs₁ i)
  have hA₂ : ∀ i, res M g₂₁ (s₁ i) = ∑ k : LP.Gen,
      resR R (homOfLE (hle₂ i)) (A₀ i k) • res M (g₂₁ ≫ g₁) (LP.gens k) := fun i =>
    (res_res M (ga i) (homOfLE (hle₂ i)) (s₁ i)).symm.trans
      (res_eq_sum_smul_res M _ _ (hA₀ i))
  choose Wb gb hxWb B₀ hB₀ using fun k : LP.Gen =>
    exists_res_eq_sum_of_basis M x hxU₂ (fun i => res M g₂₁ (s₁ i)) bas hs₂
      (res M (g₂₁ ≫ g₁) (LP.gens k))
  obtain ⟨U₃, g₃₂, hxU₃, hle₃⟩ := exists_nbhd_le' x U₂ hxU₂ Wb hxWb
  -- the data over `U₃`
  set fU : U₃ ⟶ LP.nhd := g₃₂ ≫ (g₂₁ ≫ g₁) with hfU
  set s : ρ → ToType (M.val.obj (op U₃)) := fun i => res M (g₃₂ ≫ g₂₁) (s₁ i) with hsdef
  set A : ρ → LP.Gen → ToType (R.obj.obj (op U₃)) :=
    fun i k => resR R (g₃₂ ≫ homOfLE (hle₂ i)) (A₀ i k) with hAdef
  set B : LP.Gen → ρ → ToType (R.obj.obj (op U₃)) :=
    fun k i => resR R (homOfLE (hle₃ k)) (B₀ k i) with hBdef
  have hgs : ∀ i, germ M x hxU₃ (s i) = bas i := fun i =>
    (germ_res x (g₃₂ ≫ g₂₁) hxU₃ (s₁ i)).trans (hs₁ i)
  have hA : ∀ i, s i = ∑ k : LP.Gen, A i k • res M fU (LP.gens k) := fun i =>
    (res_res M g₂₁ g₃₂ (s₁ i)).symm.trans ((res_eq_sum_smul_res M _ _ (hA₂ i)).trans
      (Finset.sum_congr rfl fun k _ => by rw [resR_resR]))
  have hB : ∀ k, res M fU (LP.gens k) = ∑ i : ρ, B k i • s i := by
    intro k
    have h1 := res_eq_sum_smul_res M (gb k) (homOfLE (hle₃ k)) (hB₀ k)
    rw [res_res, res_res] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [res_res]
    rfl
  -- the two identities, first at the level of germs
  have hgu : ∀ k, germ M x hxU₃ (res M fU (LP.gens k))
      = ∑ i : ρ, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i) • bas i := fun k => by
    rw [hB k, germ_sum_smul]
    simp only [hgs]
  have hcomb : ∀ a : LP.Gen → ToType (R.obj.obj (op U₃)),
      germ M x hxU₃ (∑ k : LP.Gen, a k • res M fU (LP.gens k))
        = ∑ i' : ρ, (∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (a k)
            * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i')) • bas i' := fun a => by
    rw [germ_sum_smul, ← sum_smul_sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [hgu k]
  have hrepr : ∀ c c' : ρ → ToType (TopCat.Presheaf.stalk R.obj x),
      ∑ i, c i • bas i = ∑ i, c' i • bas i → c = c' := fun c c' h =>
    bas.equivFun.symm.injective (by simpa only [Module.Basis.equivFun_symm_apply] using h)
  have hid1g : ∀ i i', (∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (A i k)
      * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i')) = if i = i' then 1 else 0 := fun i i' =>
    congrFun (hrepr _ (fun i'' => if i = i'' then 1 else 0)
      (((hgs i).symm.trans ((congrArg (germ M x hxU₃) (hA i)).trans (hcomb (A i)))).symm.trans
        (by simp))) i'
  have hz : ∀ l, (∑ k : LP.Gen, resR R fU (LP.rel l k) • res M fU (LP.gens k))
      = (0 : ToType (M.val.obj (op U₃))) := by
    intro l
    rw [← res_sum_smul, LP.rel_apply, res_zero]
  have hid2g : ∀ (l : LP.Rel) (i : ρ), (∑ k : LP.Gen,
      TopCat.Presheaf.germ R.obj U₃ x hxU₃ (resR R fU (LP.rel l k))
        * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i)) = 0 := fun l i =>
    congrFun (hrepr _ 0 ((hcomb fun k => resR R fU (LP.rel l k)).symm.trans
      (by rw [hz l, germ_zero]; simp))) i
  -- shrink so that both identities hold as sections
  choose Wc gc hxWc hc using fun p : ρ × ρ => exists_resR_eq_zero x hxU₃
    ((∑ k : LP.Gen, A p.1 k * B k p.2) - (if p.1 = p.2 then 1 else 0)) (by
      rw [map_sub, germR_sum_mul, hid1g p.1 p.2]
      by_cases hp : p.1 = p.2 <;> simp [hp])
  choose Wd gd hxWd hd using fun p : LP.Rel × ρ => exists_resR_eq_zero x hxU₃
    (∑ k : LP.Gen, resR R fU (LP.rel p.1 k) * B k p.2) (by
      rw [germR_sum_mul, hid2g p.1 p.2])
  obtain ⟨U₄, g₄₃, hxU₄, hle₄⟩ := exists_nbhd_le' x U₃ hxU₃
    (Sum.elim Wc Wd) (by rintro (p | p) <;> [exact hxWc p; exact hxWd p])
  refine ⟨LP, U₄, g₄₃ ≫ fU, hxU₄, fun i => res M g₄₃ (s i),
    fun i k => resR R g₄₃ (A i k), fun k i => resR R g₄₃ (B k i), ?_, ?_, ?_, ?_⟩
  · exact fun i => res_eq_sum_smul_res M fU g₄₃ (hA i)
  · intro k
    have h1 := congrArg (res M g₄₃) (hB k)
    rw [res_res, res_sum_smul] at h1
    exact h1
  · intro i i'
    have h0 : resR R g₄₃ ((∑ k : LP.Gen, A i k * B k i')
        - (if i = i' then (1 : ToType (R.obj.obj (op U₃))) else 0)) = 0 :=
      resR_comp_eq_zero (hc (i, i')) (homOfLE (hle₄ (Sum.inl (i, i'))))
    rw [resR_sub, resR_sum_mul, sub_eq_zero] at h0
    refine h0.trans ?_
    by_cases hp : i = i' <;> simp [hp, resR_one, resR_zero]
  · intro l i
    have h0 : resR R g₄₃ (∑ k : LP.Gen, resR R fU (LP.rel l k) * B k i) = 0 :=
      resR_comp_eq_zero (hd (l, i)) (homOfLE (hle₄ (Sum.inr (l, i))))
    rw [resR_sum_mul] at h0
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
    rw [resR_resR]

end Chart


/-! ### Tag 0B8J -/

section Conclusion

/-- From chart data at `x`, the chosen sections give a trivialisation of `M` on the whole
chart: taking combinations of them is injective over every open subset, and locally
surjective. -/
lemma inj_and_locally_surj_of_chart (M : SheafOfModules.{u} R) (x : X)
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    (LP : LocalPresentation M x) (U : Opens X) (fU : U ⟶ LP.nhd)
    (s : ρ → ToType (M.val.obj (op U)))
    (A : ρ → LP.Gen → ToType (R.obj.obj (op U)))
    (B : LP.Gen → ρ → ToType (R.obj.obj (op U)))
    (hA : ∀ i, s i = ∑ k : LP.Gen, A i k • res M fU (LP.gens k))
    (hB : ∀ k, res M fU (LP.gens k) = ∑ i : ρ, B k i • s i)
    (hid1 : ∀ i i', ∑ k : LP.Gen, A i k * B k i' = if i = i' then 1 else 0)
    (hid2 : ∀ l i, ∑ k : LP.Gen, resR R fU (LP.rel l k) * B k i = 0) :
    (∀ ⦃V : Opens X⦄ (f : V ⟶ U), Function.Injective
        (fun c : ρ → ToType (R.obj.obj (op V)) => ∑ i : ρ, c i • res M f (s i)))
    ∧ (∀ ⦃V : Opens X⦄ (f : V ⟶ U) (t : ToType (M.val.obj (op V))) (y : X), y ∈ V →
        ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ ∃ c : ρ → ToType (R.obj.obj (op W)),
          res M h t = ∑ i : ρ, c i • res M (h ≫ f) (s i)) := by
  classical
  -- the restriction of `s` to any open generates freely: first the kernel statement
  have hker : ∀ ⦃V : Opens X⦄ (f : V ⟶ U) (a : ρ → ToType (R.obj.obj (op V))),
      (∑ i : ρ, a i • res M f (s i) = 0) → a = 0 := by
    intro V f a ha
    funext i
    refine eq_zero_of_locally_zero (a i) fun y hy => ?_
    have hres : ∀ i', res M f (s i')
        = ∑ k : LP.Gen, resR R f (A i' k) • res M (f ≫ fU) (LP.gens k) := fun i' =>
      res_eq_sum_smul_res M fU f (hA i')
    have hzrel : (∑ k : LP.Gen,
        (∑ i' : ρ, a i' * resR R f (A i' k)) • res M (f ≫ fU) (LP.gens k)) = 0 := by
      rw [← sum_smul_sum_smul]
      exact Eq.trans (Finset.sum_congr rfl fun i' _ => by rw [← hres i']) ha
    obtain ⟨W, h, hyW, b, hb⟩ :=
      LP.relations (f ≫ fU) (fun k => ∑ i' : ρ, a i' * resR R f (A i' k)) hzrel y hy
    refine ⟨W, h, hyW, ?_⟩
    -- compute `resR R h (a i)` in two ways
    have hz : ∀ k, resR R h (∑ i' : ρ, a i' * resR R f (A i' k))
        = ∑ i' : ρ, resR R h (a i') * resR R (h ≫ f) (A i' k) := fun k => by
      rw [resR_sum_mul]
      exact Finset.sum_congr rfl fun i' _ => by rw [resR_resR]
    have hone : ∀ i', (∑ k : LP.Gen, resR R (h ≫ f) (A i' k) * resR R (h ≫ f) (B k i))
        = if i' = i then 1 else 0 := by
      intro i'
      rw [← resR_sum_mul, hid1 i' i]
      by_cases hp : i' = i <;> simp [hp, resR_one, resR_zero]
    have hzero : ∀ l, (∑ k : LP.Gen,
        resR R (h ≫ (f ≫ fU)) (LP.rel l k) * resR R (h ≫ f) (B k i)) = 0 := fun l => by
      have h0 := congrArg (resR R (h ≫ f)) (hid2 l i)
      rw [resR_sum_mul, resR_zero] at h0
      simp only [resR_resR] at h0
      exact h0
    calc resR R h (a i)
        = ∑ i' : ρ, resR R h (a i') * (if i' = i then (1 : _) else 0) :=
          (sum_mul_ite (fun i' => resR R h (a i')) i).symm
      _ = ∑ i' : ρ, resR R h (a i')
            * (∑ k : LP.Gen, resR R (h ≫ f) (A i' k) * resR R (h ≫ f) (B k i)) :=
          Finset.sum_congr rfl fun i' _ => by rw [hone i']
      _ = ∑ k : LP.Gen, (∑ i' : ρ, resR R h (a i') * resR R (h ≫ f) (A i' k))
            * resR R (h ≫ f) (B k i) := (sum_mul_sum_mul _ _ _).symm
      _ = ∑ k : LP.Gen, (∑ l : LP.Rel,
            b l * resR R (h ≫ (f ≫ fU)) (LP.rel l k)) * resR R (h ≫ f) (B k i) :=
          Finset.sum_congr rfl fun k _ => by rw [← hz k, hb k]
      _ = ∑ l : LP.Rel, b l * (∑ k : LP.Gen,
            resR R (h ≫ (f ≫ fU)) (LP.rel l k) * resR R (h ≫ f) (B k i)) :=
          sum_mul_sum_mul _ _ _
      _ = 0 := by
          refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) Finset.sum_const_zero
          rw [hzero l, mul_zero]
  refine ⟨fun V f a a' haa => ?_, fun V f t y hy => ?_⟩
  · have h0 : a - a' = 0 := by
      refine hker f (a - a') ?_
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [show (∑ i : ρ, a i • res M f (s i)) = ∑ i : ρ, a' i • res M f (s i) from haa, sub_self]
    exact sub_eq_zero.mp h0
  · obtain ⟨W, h, hyW, c, hc⟩ := LP.generates (f ≫ fU) t y hy
    refine ⟨W, h, hyW, fun i => ∑ k : LP.Gen, c k * resR R (h ≫ f) (B k i), ?_⟩
    refine hc.trans (Eq.trans (Finset.sum_congr rfl fun k _ => ?_)
      (sum_smul_sum_smul c (fun k i => resR R (h ≫ f) (B k i))
        (fun i => res M (h ≫ f) (s i))))
    refine congrArg (fun y => c k • y) ?_
    have h2 := congrArg (res M (h ≫ f)) (hB k)
    rw [res_res, res_sum_smul] at h2
    exact h2

/-- **Stacks Project, Tag 0B8J**, in terms of a basis of the stalk: if `M` is a finitely
presented sheaf of modules whose stalk at `x` is free on a finite basis, then `M` is isomorphic
to a free sheaf of modules on a neighbourhood of `x`. -/
theorem nonempty_over_iso_free_of_stalk_basis (M : SheafOfModules.{u} R)
    [M.IsFinitePresentation] (x : X) {ρ : Type u} [Finite ρ]
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (M.over U ≅ free (R := R.over U) ρ) := by
  classical
  cases nonempty_fintype ρ
  obtain ⟨LP, U, fU, hxU, s, A, B, hA, hB, hid1, hid2⟩ := exists_chart M x bas
  obtain ⟨hinj, hsurj⟩ :=
    inj_and_locally_surj_of_chart M x LP U fU s A B hA hB hid1 hid2
  exact ⟨U, hxU, nonempty_over_iso_free_of_inj_of_surj M s hinj hsurj⟩

end Conclusion

end Opens

/-! ### The statement of Tag 0B8J -/

/-- **Stacks Project, Tag 0B8J.** Let `(X, 𝒪_X)` be a ringed space and let `M` be a finitely
presented sheaf of `𝒪_X`-modules. If the stalk of `M` at a point `x` is free of rank `r` over
`𝒪_{X, x}`, then the restriction of `M` to some open neighbourhood of `x` is isomorphic to the
free sheaf of modules of rank `r`. -/
@[stacks 0B8J, ega "0 5.2.7" "free case G = O^r"]
theorem exists_iso_free_over_of_stalk_iso_free {X : TopCat.{u}}
    {R : TopCat.Sheaf RingCat.{u} X} (M : SheafOfModules.{u} R)
    (hM : M.IsFinitePresentation) (x : X) (r : ℕ)
    (hx : Nonempty
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x) ≃ₗ[ToType (R.presheaf.stalk x)]
        (ULift.{u} (Fin r) →₀ ToType (R.presheaf.stalk x)))) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  have := hM
  obtain ⟨e⟩ := hx
  exact nonempty_over_iso_free_of_stalk_basis M x (Module.Basis.ofRepr e)

end Stacks.SheafOfModules
