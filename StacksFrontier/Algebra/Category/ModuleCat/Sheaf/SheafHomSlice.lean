module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# The sheaf-hom out of a finitely presented module is locally a kernel

Let `(X, 𝒪)` be a ringed space and let `F`, `G` be sheaves of `𝒪`-modules with `F` of finite
presentation. [Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) asserts that the
internal hom `SheafHom(F, G)` is, on a neighbourhood of every point, the kernel of a map
between two finite direct sums of copies of `G`, and consequently that `SheafHom(F, G)` is
coherent as soon as `G` is. Both assertions are proved here.

The key input is the **comparison between the restriction of the sheaf-hom to an open and the
hom taken on the slice site**: a section of `SheafHom(F, G)|_U` over an object `V` of `Over U`
*is* a morphism `F|_{V.left} ⟶ G|_{V.left}` of sheaves of modules on the slice site at
`V.left`. That is `sheafHomOverEquiv`.

## Main definitions

* `Stacks.SheafOfModules.sheafHomOverEquiv`: **the comparison.** Sections over `V : Over U` of
  the restriction `SheafHom(F, G)|_U` are exactly the morphisms `F|_{V.left} ⟶ G|_{V.left}`.
* `Stacks.SheafOfModules.evalAt`: for a section `s` of `F` over `U`, the morphism
  `SheafHom(F, G)|_U ⟶ G|_U` evaluating a local morphism at `s`.
* `Stacks.SheafOfModules.sheafHomToSigma`: the comparison `Θ` of Tag 01CQ, assembled from
  `evalAt` at the members of a finite family of sections of `F` over `U`.
* `Stacks.SheafOfModules.homCoords`: the family of sections of `G` over `W` that a morphism
  `F|_W ⟶ G|_W` attaches to a family of sections of `F`.
* `Stacks.SheafOfModules.sigmaProj`: the coordinate projections of a coproduct of copies of a
  single sheaf of modules, and `sigmaMatrix`, the morphism between two such coproducts given by
  a matrix of sections of the sheaf of rings.
* `Stacks.SheafOfModules.smulSelf`: multiplication by a section of the sheaf of rings over `U`,
  as an endomorphism of a sheaf of modules on the slice site at `U`.

## Main results

* `Stacks.SheafOfModules.sheafHom_locallyKernelFiniteCoproduct` is **Tag 01CQ (1)**: around
  every point, `SheafHom(F, G)|_U` is isomorphic to the kernel of a morphism
  `G|_U^{⊕m} ⟶ G|_U^{⊕n}`.
* `Stacks.SheafOfModules.sheafHom_isCoherent` is **Tag 01CQ (2)**: the first assertion fed
  through Tag 01BY, in the form `isCoherent_of_locallyKernelFiniteCoproduct`.
* `Stacks.SheafOfModules.nonempty_sheafHomOver_iso_kernel` is the first assertion with the
  presentation data supplied explicitly: given `P : LocalPresentation F x`, the restriction
  `SheafHom(F, G)|_{P.nhd}` is the kernel of `sigmaMatrix` applied to the relation matrix
  `P.rel`.
* `Stacks.SheafOfModules.homCoords_injective` and
  `Stacks.SheafOfModules.exists_homCoords_eq`: a morphism `F|_W ⟶ G|_W` is determined by, and
  can be prescribed by, its values on a generating family — the second one subject to the
  relations, via `Stacks.SheafOfModules.kernelι_comp_freeToOver_eq_zero`.
* `Stacks.SheafOfModules.eq_zero_of_locally_zero'`: a section of a sheaf of modules vanishing
  near every point vanishes. This is the module analogue of
  `Stacks.SheafOfModules.eq_zero_of_locally_zero`.

## Implementation notes

**The comparison is stated on sections.** The Stacks statement is
`SheafHom(F, G)|_U ≅ SheafHom_{𝒪|_U}(F|_U, G|_U)`, an isomorphism of sheaves of modules on the
slice site `Over U`; writing it that way requires identifying the slice site of `Over U` at `V`
with the slice site of `X` at `V.left`, along `CategoryTheory.Over.iteratedSliceEquiv`. On
sections no such transport is needed: the sections over `V` of the restricted sheaf-hom are
directly morphisms `F.over V.left ⟶ G.over V.left`, and the comparison is `α ↦ ⟨α⟩`, an
`Equiv` by structure eta. `sheafHomOverEquiv_eval` reads it off through `evalSection`. The
sheaf-level form, [Stacks, Tag 0E8H], is `Stacks.SheafOfModules.InternalHom.internalHomOverIso`.

**The site is the opens of a space, not a general site.** `internalHom` of Tag 03EM and
`Stacks.SheafOfModules.sheafHom` are both available over an arbitrary site, so the comparison
could be *stated* at that generality. The proof of Tag 01CQ cannot: it unpacks the finite
presentation into `Stacks.SheafOfModules.LocalPresentation` data — explicit generators and a
relation matrix over `R(U)` — which exists only for the site `Opens X`, and it uses twice over
that any two morphisms of `Opens X` are *definitionally* equal (so that `Over.mk Y.hom = Y` and
`Over.mk (W.hom.left ≫ V.hom) = W.left` hold by `rfl`, which is exactly what makes the
comparison structure eta rather than a transport).

**Universes.** Everything is in the single universe `u` that the site `Opens X` forces:
`X : TopCat.{u}`, `𝒪 : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}`, modules in `SheafOfModules.{u}`.

**Decidability of the index types** appears in the statements that mention `sigmaProj` or
`sigmaMatrix`, because the coordinate projections are built from `if j = i then 𝟙 else 0`. The
two `@[stacks 01CQ]` theorems do not mention them: they existentially quantify over the
morphism and instantiate the decidability classically.

**The coherence consequence uses `Stacks.SheafOfModules.IsCoherent`**, which is the predicate
that `isCoherent_of_locallyKernelFiniteCoproduct` produces.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u

namespace Stacks.SheafOfModules

/-! ### Sections of a sheaf of modules that vanish locally -/

section LocallyZero

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- A section of a sheaf of modules which vanishes on a neighbourhood of every point of its
domain vanishes. -/
lemma eq_zero_of_locally_zero' (M : SheafOfModules.{u} R) {V : Opens X}
    (m : ToType (M.val.obj (op V)))
    (hm : ∀ y ∈ V, ∃ (W : Opens X) (h : W ⟶ V), y ∈ W ∧ res M h m = 0) : m = 0 := by
  refine TopCat.Presheaf.section_ext
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) V m 0 fun y hy => ?_
  obtain ⟨W, h, hyW, h0⟩ := hm y hy
  calc TopCat.Presheaf.germ M.val.presheaf V y hy m
      = TopCat.Presheaf.germ M.val.presheaf W y hyW (res M h m) :=
        (TopCat.Presheaf.germ_res_apply M.val.presheaf h y hyW m).symm
    _ = 0 := by rw [h0]; exact map_zero _
    _ = TopCat.Presheaf.germ M.val.presheaf V y hy 0 := (map_zero _).symm

end LocallyZero

/-! ### Coordinates on a finite coproduct of copies of one sheaf of modules -/

section SigmaCoords

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  (N : SheafOfModules.{u} S) {ι : Type u} [DecidableEq ι] [HasCoproduct (fun _ : ι => N)]

/-- The `i`-th coordinate projection of a coproduct of copies of a single sheaf of modules. -/
noncomputable def sigmaProj (i : ι) : (∐ fun _ : ι => N) ⟶ N :=
  Sigma.desc fun j => if j = i then 𝟙 N else 0

/-- The `j`-th coproduct inclusion followed by the `i`-th coordinate projection is the identity
if `j = i` and zero otherwise. -/
lemma ι_comp_sigmaProj (i j : ι) :
    Sigma.ι (fun _ : ι => N) j ≫ sigmaProj N i = if j = i then 𝟙 N else 0 :=
  Sigma.ι_desc _ _

/-- The `i`-th coordinate projection is a retraction of the `i`-th coproduct inclusion. -/
lemma ι_comp_sigmaProj_self (i : ι) :
    Sigma.ι (fun _ : ι => N) i ≫ sigmaProj N i = 𝟙 N := by
  simp [ι_comp_sigmaProj]

/-- The `i`-th coordinate projection vanishes on the `j`-th coproduct inclusion for `j ≠ i`. -/
lemma ι_comp_sigmaProj_of_ne {i j : ι} (h : j ≠ i) :
    Sigma.ι (fun _ : ι => N) j ≫ sigmaProj N i = 0 := by
  simp [ι_comp_sigmaProj, h]

/-- The `l`-th coordinate of a sum of morphisms followed by the coproduct inclusions is the
`l`-th summand. -/
private lemma sum_comp_ι_comp_sigmaProj [Fintype ι] {P : SheafOfModules.{u} S}
    (e : ι → (P ⟶ N)) (l : ι) :
    (∑ k : ι, e k ≫ Sigma.ι (fun _ : ι => N) k) ≫ sigmaProj N l = e l := by
  rw [Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem l (Finset.mem_univ l) (fun b _ hb => by
      rw [Category.assoc, ι_comp_sigmaProj_of_ne N hb, comp_zero]),
    Category.assoc, ι_comp_sigmaProj_self, Category.comp_id]

/-- The identity of a finite coproduct of copies of `N` is the sum of the coordinate projections
followed by the coproduct inclusions. -/
lemma id_sigma_eq_sum [Fintype ι] :
    𝟙 (∐ fun _ : ι => N) = ∑ i : ι, sigmaProj N i ≫ Sigma.ι (fun _ : ι => N) i := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [Category.comp_id, Preadditive.comp_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun b _ hb => by
      rw [← Category.assoc, ι_comp_sigmaProj_of_ne N (Ne.symm hb), zero_comp]),
    ← Category.assoc, ι_comp_sigmaProj_self, Category.id_comp]

/-- A morphism into a finite coproduct of copies of one sheaf of modules vanishes as soon as
all of its coordinates do. -/
lemma eq_zero_of_comp_sigmaProj [Finite ι] {P : SheafOfModules.{u} S}
    (φ : P ⟶ ∐ fun _ : ι => N) (hφ : ∀ i : ι, φ ≫ sigmaProj N i = 0) : φ = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← Category.comp_id φ, id_sigma_eq_sum, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Category.assoc, hφ i, zero_comp]

/-- A section of a finite coproduct of copies of one sheaf of modules is determined by its
coordinates. -/
lemma sigma_section_ext [Finite ι] (V : Cᵒᵖ)
    (z z' : ToType ((∐ fun _ : ι => N).val.obj V))
    (h : ∀ i : ι, (sigmaProj N i).val.app V z = (sigmaProj N i).val.app V z') : z = z' := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have key : ∀ y : ToType ((∐ fun _ : ι => N).val.obj V),
      (∑ i : ι, sigmaProj N i ≫ Sigma.ι (fun _ : ι => N) i).val.app V y = y := fun y => by
    rw [← id_sigma_eq_sum]
    rfl
  rw [← key z, ← key z', app_sum, app_sum]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun y => (Sigma.ι (fun _ : ι => N) i).val.app V y) (h i)

/-- Equal morphisms of sheaves of modules agree on every section. -/
private lemma val_app_apply_congr {P Q : SheafOfModules.{u} S} {φ ψ : P ⟶ Q} (e : φ = ψ)
    (V : Cᵒᵖ) (z : ToType (P.val.obj V)) : φ.val.app V z = ψ.val.app V z := by
  rw [e]

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A monomorphism of sheaves of modules is injective on every group of sections. -/
lemma injective_val_app_of_mono_evaluation {P Q : SheafOfModules.{u} S} (φ : P ⟶ Q) [Mono φ] (V :
Cᵒᵖ) :
    Function.Injective (φ.val.app V) := by
  have : (_root_.SheafOfModules.evaluation S V).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  rw [← ModuleCat.mono_iff_injective]
  exact (_root_.SheafOfModules.evaluation S V).map_mono φ

/-- A morphism of sheaves of modules which is bijective on every group of sections is an
isomorphism. -/
lemma isIso_of_bijective_app {P Q : SheafOfModules.{u} S} (φ : P ⟶ Q)
    (h : ∀ V : Cᵒᵖ, Function.Injective (φ.val.app V) ∧ Function.Surjective (φ.val.app V)) :
    IsIso φ :=
  have : Mono φ :=
    (SheafOfModules.forget S).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (f := φ.val) fun {V} => (h V).1)
  have : Epi φ :=
    (SheafOfModules.forget S).epi_of_epi_map
      (PresheafOfModules.epi_of_surjective (f := φ.val) fun {V} => (h V).2)
  isIso_of_mono_of_epi φ

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The map into a kernel induced by a morphism killed by `g` is injective on sections over `V`
as soon as that morphism is. -/
lemma injective_kernelLift_app {P Q Q' : SheafOfModules.{u} S} (g : Q ⟶ Q') (φ : P ⟶ Q)
    (hφ : φ ≫ g = 0) (V : Cᵒᵖ) (hinj : Function.Injective (φ.val.app V)) :
    Function.Injective ((kernel.lift g φ hφ).val.app V) := by
  have h : ∀ y, (kernel.ι g).val.app V ((kernel.lift g φ hφ).val.app V y) = φ.val.app V y :=
    fun y => val_app_apply_congr (kernel.lift_ι g φ hφ) V y
  intro a b hab
  refine hinj ?_
  rw [← h a, ← h b, hab]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The map into a kernel induced by a morphism killed by `g` is surjective on sections over
`V` as soon as that morphism hits every section killed by `g`. -/
lemma surjective_kernelLift_app {P Q Q' : SheafOfModules.{u} S} (g : Q ⟶ Q') (φ : P ⟶ Q)
    (hφ : φ ≫ g = 0) (V : Cᵒᵖ)
    (hsurj : ∀ z : ToType (Q.val.obj V), g.val.app V z = 0 → ∃ a, φ.val.app V a = z) :
    Function.Surjective ((kernel.lift g φ hφ).val.app V) := by
  intro w
  obtain ⟨a, ha⟩ := hsurj ((kernel.ι g).val.app V w)
    (val_app_apply_congr (kernel.condition g) V w)
  refine ⟨a, injective_val_app_of_mono_evaluation (kernel.ι g) V ?_⟩
  rw [show (kernel.ι g).val.app V ((kernel.lift g φ hφ).val.app V a) = φ.val.app V a from
    val_app_apply_congr (kernel.lift_ι g φ hφ) V a, ha]

end SigmaCoords

/-! ### Multiplication by a section of the sheaf of rings -/

section SmulSelf

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- Multiplication by a section `a` of the sheaf of rings over `U`, as an endomorphism of a
sheaf of modules on the slice site at `U`. Commutativity of the sheaf of rings is what makes
this `R|_U`-linear rather than merely additive. -/
noncomputable def smulSelf
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} (a : ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) : N ⟶ N where
  val :=
    { app := fun V => ModuleCat.ofHom
        { toFun := fun z => resROver R V.unop a • z
          map_add' := fun z z' => smul_add _ z z'
          map_smul' := fun r z => by
            change resROver R V.unop a • (r • z) = r • (resROver R V.unop a • z)
            rw [smul_smul, smul_smul]
            exact congrArg (fun b => b • z) (hR V.unop.left (resROver R V.unop a) r) }
      naturality := fun {V V'} g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
        change resROver R V'.unop a • N.val.map g z = N.val.map g (resROver R V.unop a • z)
        rw [PresheafOfModules.map_smul]
        refine congrArg (fun b => b • N.val.map g z) ?_
        change resR R V'.unop.hom a = resR R g.unop.left (resR R V.unop.hom a)
        rw [resR_resR]
        exact congrArg (fun k : V'.unop.left ⟶ U => resR R k a) (Subsingleton.elim _ _) }

/-- On sections over `V`, `smulSelf hR a N` is multiplication by the restriction of `a`. -/
@[simp]
lemma smulSelf_val_app_apply
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} (a : ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) (V : (Over U)ᵒᵖ) (z : ToType (N.val.obj V)) :
    (smulSelf hR a N).val.app V z = resROver R V.unop a • z := rfl

/-- **The morphism between finite coproducts of copies of one sheaf of modules given by a
matrix of sections of the sheaf of rings.** Its `(l, k)` component is multiplication by
`rel l k`. -/
noncomputable def sigmaMatrix
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} {Gen Rel : Type u} [DecidableEq Gen] [Fintype Gen] [DecidableEq Rel]
    [Fintype Rel] (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) [HasCoproduct (fun _ : Gen => N)]
    [HasCoproduct (fun _ : Rel => N)] :
    (∐ fun _ : Gen => N) ⟶ (∐ fun _ : Rel => N) :=
  ∑ k : Gen, ∑ l : Rel,
    sigmaProj N k ≫ smulSelf hR (rel l k) N ≫ Sigma.ι (fun _ : Rel => N) l

/-- The `l`-th coordinate of the matrix morphism is the sum over `k` of the `k`-th coordinate
followed by multiplication by `rel l k`. -/
lemma sigmaMatrix_comp_sigmaProj
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} {Gen Rel : Type u} [DecidableEq Gen] [Fintype Gen] [DecidableEq Rel]
    [Fintype Rel] (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) [HasCoproduct (fun _ : Gen => N)]
    [HasCoproduct (fun _ : Rel => N)] (l : Rel) :
    sigmaMatrix hR rel N ≫ sigmaProj N l =
      ∑ k : Gen, sigmaProj N k ≫ smulSelf hR (rel l k) N := by
  rw [sigmaMatrix, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa only [Category.assoc] using
    sum_comp_ι_comp_sigmaProj N (fun l => sigmaProj N k ≫ smulSelf hR (rel l k) N) l

/-- Restricting a section of the sheaf of rings to an object `V` of the slice site over `U` is
restricting it along `V.hom`. -/
lemma resROver_eq_resR (R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u})
    {U : Opens X} (V : Over U) (a : ToType (R.obj.obj (op U))) :
    resROver R V a = resR R V.hom a := rfl

/-- The coordinates of the matrix morphism on sections: the `l`-th coordinate of the image of
a section `z` is the `l`-th row of the matrix applied to the coordinates of `z`. -/
lemma sigmaProj_sigmaMatrix_app
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} {Gen Rel : Type u} [DecidableEq Gen] [Fintype Gen] [DecidableEq Rel]
    [Fintype Rel] (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) [HasCoproduct (fun _ : Gen => N)]
    [HasCoproduct (fun _ : Rel => N)] (V : (Over U)ᵒᵖ)
    (z : ToType ((∐ fun _ : Gen => N).val.obj V)) (l : Rel) :
    (sigmaProj N l).val.app V ((sigmaMatrix hR rel N).val.app V z) =
      ∑ k : Gen, resROver R V.unop (rel l k) • (sigmaProj N k).val.app V z := by
  have h := congrArg (fun φ : (∐ fun _ : Gen => N) ⟶ N => φ.val.app V z)
    (sigmaMatrix_comp_sigmaProj hR rel N l)
  rwa [app_sum] at h

/-- A section of the source killed by the matrix morphism has coordinates annihilated by every
row of the matrix. -/
lemma sum_resROver_smul_sigmaProj_eq_zero
    (hR : ∀ (W : Opens X) (b c : ToType (R.obj.obj (op W))), b * c = c * b)
    {U : Opens X} {Gen Rel : Type u} [DecidableEq Gen] [Fintype Gen] [DecidableEq Rel]
    [Fintype Rel] (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (N : SheafOfModules.{u} (R.over U)) [HasCoproduct (fun _ : Gen => N)]
    [HasCoproduct (fun _ : Rel => N)] (V : (Over U)ᵒᵖ)
    (z : ToType ((∐ fun _ : Gen => N).val.obj V))
    (hz : (sigmaMatrix hR rel N).val.app V z = 0) (l : Rel) :
    ∑ k : Gen, resROver R V.unop (rel l k) • (sigmaProj N k).val.app V z = 0 := by
  rw [← sigmaProj_sigmaMatrix_app hR rel N V z l, hz]
  exact map_zero _

end SmulSelf

/-! ### Morphisms out of a locally presented sheaf of modules -/

section HomDescription

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
  (F G : SheafOfModules.{u} R)

/-- A global section of `M.over W` is determined by its value over `W`. -/
lemma overSection_injective (M : SheafOfModules.{u} R) {W : Opens X} :
    Function.Injective (overSection M (U := W)) := fun m m' hmm => by
  have h : res M (𝟙 W) m = res M (𝟙 W) m' :=
    congrArg (fun t : (M.over W).sections => t.eval (op (Over.mk (𝟙 W)))) hmm
  rwa [res_id, res_id] at h

/-- The global sections of `M.over U` attached by `freeToOver` to a family of sections. -/
lemma freeHomEquiv_freeToOver (M : SheafOfModules.{u} R) {U : Opens X} {ι : Type u}
    (s : ι → ToType (M.val.obj (op U))) (k : ι) :
    freeHomEquiv (M.over U) (freeToOver M s) k = overSection M (s k) := by
  rw [freeToOver, (freeHomEquiv (M.over U)).apply_symm_apply]

/-- The family of sections of `G` over `W` attached to a morphism `F|_W ⟶ G|_W` by a family
`s` of sections of `F` over `U`: the `k`-th member is the value of the morphism on `s k`
restricted to `W`. -/
noncomputable def homCoords {U W : Opens X} (h : W ⟶ U) {ι : Type u}
    (s : ι → ToType (F.val.obj (op U))) (φ : F.over W ⟶ G.over W) (k : ι) :
    ToType (G.val.obj (op W)) :=
  φ.val.app (op (Over.mk (𝟙 W))) (res F h (s k))

/-- Reading `homCoords` through the free presentation: the `k`-th global section attached to
`freeToOver F (s · |_W) ≫ φ` is the `k`-th member of `homCoords`. -/
lemma freeHomEquiv_freeToOver_comp {U W : Opens X} (h : W ⟶ U) {ι : Type u}
    (s : ι → ToType (F.val.obj (op U))) (φ : F.over W ⟶ G.over W) (k : ι) :
    freeHomEquiv (G.over W) (freeToOver F (fun i => res F h (s i)) ≫ φ) k =
      overSection G (homCoords F G h s φ k) := by
  rw [freeHomEquiv_comp_apply, freeHomEquiv_freeToOver]
  have hv : (sectionsMap φ (overSection F (res F h (s k)))).eval (op (Over.mk (𝟙 W))) =
      homCoords F G h s φ k := by
    have hr : res F (𝟙 W) (res F h (s k)) = res F h (s k) := res_id F _
    exact congrArg (fun y => φ.val.app (op (Over.mk (𝟙 W))) y) hr
  rw [← hv]
  exact (overSection_eval_eq G (sectionsMap φ (overSection F (res F h (s k))))).symm

/-- **A morphism out of `F|_W` is determined by its values on a generating family.** -/
lemma homCoords_injective {U W : Opens X} (h : W ⟶ U) {ι : Type u}
    (s : ι → ToType (F.val.obj (op U)))
    [Epi (freeToOver F (fun i => res F h (s i)))] :
    Function.Injective (homCoords F G h s) := by
  intro φ φ' hφ
  refine (cancel_epi (freeToOver F (fun i => res F h (s i)))).1
    ((freeHomEquiv (G.over W)).injective (funext fun k => ?_))
  rw [freeHomEquiv_freeToOver_comp, freeHomEquiv_freeToOver_comp, congrFun hφ k]

/-- **Realizing a family of sections of `G` as the values of a morphism `F|_W ⟶ G|_W`**, once
it is known that the relations between the generators are killed. -/
lemma exists_homCoords_eq {U W : Opens X} (h : W ⟶ U) {ι : Type u}
    (s : ι → ToType (F.val.obj (op U)))
    [Epi (freeToOver F (fun i => res F h (s i)))]
    (c : ι → ToType (G.val.obj (op W)))
    (hc : kernel.ι (freeToOver F (fun i => res F h (s i))) ≫ freeToOver G c = 0) :
    ∃ φ : F.over W ⟶ G.over W, homCoords F G h s φ = c := by
  refine ⟨Abelian.epiDesc _ (freeToOver G c) hc, funext fun k => ?_⟩
  have h1 := Abelian.comp_epiDesc (freeToOver F (fun i => res F h (s i))) (freeToOver G c) hc
  have h2 := congrFun (congrArg (freeHomEquiv (G.over W)) h1) k
  rw [freeHomEquiv_freeToOver_comp, freeHomEquiv_freeToOver] at h2
  exact overSection_injective G h2

/-- If a tuple `z` of sections of the sheaf of rings over `V₀` kills the generators then it
kills any family `c` annihilated by the relation matrix. -/
lemma res_sum_smul_eq_zero_of_relations {U W V₀ : Opens X} (h : W ⟶ U) (f₀ : V₀ ⟶ W)
    {Gen Rel : Type u} [Fintype Gen] [Fintype Rel]
    (s : Gen → ToType (F.val.obj (op U))) (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (hrels : ∀ ⦃V : Opens X⦄ (f : V ⟶ U) (z : Gen → ToType (R.obj.obj (op V))),
      (∑ k : Gen, z k • res F f (s k) = 0) → ∀ y ∈ V,
      ∃ (W' : Opens X) (g : W' ⟶ V), y ∈ W' ∧ ∃ b : Rel → ToType (R.obj.obj (op W')),
        ∀ k : Gen, resR R g (z k) = ∑ l : Rel, b l * resR R (g ≫ f) (rel l k))
    (c : Gen → ToType (G.val.obj (op W)))
    (hc : ∀ l : Rel, ∑ k : Gen, resR R h (rel l k) • c k = 0)
    (z : Gen → ToType (R.obj.obj (op V₀)))
    (hz : ∑ k : Gen, z k • res F (f₀ ≫ h) (s k) = 0) :
    ∑ k : Gen, z k • res G f₀ (c k) = 0 := by
  refine eq_zero_of_locally_zero' G _ fun y hy => ?_
  obtain ⟨W', g, hyW', b, hb⟩ := hrels (f₀ ≫ h) z hz y hy
  refine ⟨W', g, hyW', ?_⟩
  have hres : ∀ (l : Rel) (k : Gen),
      resR R (g ≫ f₀) (resR R h (rel l k)) = resR R (g ≫ f₀ ≫ h) (rel l k) := by
    intro l k
    rw [resR_resR]
    exact congrArg (fun k' : W' ⟶ U => resR R k' (rel l k)) (Subsingleton.elim _ _)
  have hinner : ∀ l : Rel,
      ∑ k : Gen, resR R (g ≫ f₀ ≫ h) (rel l k) • res G (g ≫ f₀) (c k) = 0 := by
    intro l
    have h0 : res G (g ≫ f₀) (∑ k : Gen, resR R h (rel l k) • c k) = 0 := by
      rw [hc l, res_zero]
    rw [res_sum_smul] at h0
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
    exact congrArg (fun a => a • res G (g ≫ f₀) (c k)) (hres l k).symm
  have hstep : ∀ k : Gen, resR R g (z k) • res G g (res G f₀ (c k)) =
      (∑ l : Rel, b l * resR R (g ≫ f₀ ≫ h) (rel l k)) • res G (g ≫ f₀) (c k) := by
    intro k
    rw [hb k, res_res]
  rw [res_sum_smul]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => hstep k) ?_
  rw [← sum_smul_sum_smul b (fun l k => resR R (g ≫ f₀ ≫ h) (rel l k))
    (fun k => res G (g ≫ f₀) (c k))]
  exact Finset.sum_eq_zero fun l _ => by rw [hinner l, smul_zero]

/-- **The relations of a local presentation kill the morphism out of the free sheaf attached to
a family of sections of `G` satisfying the matrix relations.** -/
lemma kernelι_comp_freeToOver_eq_zero {U W : Opens X} (h : W ⟶ U) {Gen Rel : Type u}
    [Fintype Gen] [Fintype Rel]
    (s : Gen → ToType (F.val.obj (op U))) (rel : Rel → Gen → ToType (R.obj.obj (op U)))
    (hrels : ∀ ⦃V : Opens X⦄ (f : V ⟶ U) (z : Gen → ToType (R.obj.obj (op V))),
      (∑ k : Gen, z k • res F f (s k) = 0) → ∀ y ∈ V,
      ∃ (W' : Opens X) (g : W' ⟶ V), y ∈ W' ∧ ∃ b : Rel → ToType (R.obj.obj (op W')),
        ∀ k : Gen, resR R g (z k) = ∑ l : Rel, b l * resR R (g ≫ f) (rel l k))
    (c : Gen → ToType (G.val.obj (op W)))
    (hc : ∀ l : Rel, ∑ k : Gen, resR R h (rel l k) • c k = 0) :
    kernel.ι (freeToOver F (fun i => res F h (s i))) ≫ freeToOver G c = 0 := by
  classical
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Y =>
    ModuleCat.hom_ext (LinearMap.ext fun w => ?_))
  have key : ∀ (V₀ : Opens X) (f₀ : V₀ ⟶ W) (z : Gen → ToType (R.obj.obj (op V₀))),
      (freeToOver F (fun i => res F h (s i))).val.app (op (Over.mk f₀)) (ofCoords f₀ z) = 0 →
      (freeToOver G c).val.app (op (Over.mk f₀)) (ofCoords f₀ z) = 0 := by
    intro V₀ f₀ z he
    have hA : ∑ k : Gen, z k • res F (f₀ ≫ h) (s k) =
        ∑ k : Gen, z k • res F f₀ (res F h (s k)) :=
      Finset.sum_congr rfl fun k _ => congrArg (fun y => z k • y) (res_res F h f₀ (s k)).symm
    have hB := freeToOver_app_ofCoords F (fun i => res F h (s i)) f₀ z
    exact (freeToOver_app_ofCoords G c f₀ z).trans
      (res_sum_smul_eq_zero_of_relations F G h f₀ s rel hrels c hc z
        (hA.trans (hB.symm.trans he)))
  have hcond : (freeToOver F (fun i => res F h (s i))).val.app Y
      ((kernel.ι (freeToOver F fun i => res F h (s i))).val.app Y w) = 0 :=
    val_app_apply_congr (kernel.condition (freeToOver F fun i => res F h (s i))) Y w
  have hez := ofCoords_coords (ι := Gen) (R := R) Y.unop.hom
    ((kernel.ι (freeToOver F fun i => res F h (s i))).val.app Y w)
  have hkey := key Y.unop.left Y.unop.hom
    (coords (R := R) Y.unop.hom
      ((kernel.ι (freeToOver F fun i => res F h (s i))).val.app Y w))
    (by rw [hez]; exact hcond)
  rwa [hez] at hkey

end HomDescription

/-! ### The sheaf-hom restricted to an open -/

section SliceHom

variable {X : TopCat.{u}} (𝒪 : (Opens (X : Type u))ᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology (X : Type u))
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  (F G : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- **The sheaf-hom restricted to an open, compared with the hom on the slice site.**

A section over `V : Over U` of the restriction `SheafHom(F, G)|_U` *is* a morphism
`F|_{V.left} ⟶ G|_{V.left}` of sheaves of modules on the slice site at `V.left`. -/
noncomputable def sheafHomOverEquiv (U : Opens X) (V : Over U) :
    ToType (((sheafHom 𝒪 h𝒪 F G).over U).val.obj (op V)) ≃
      (F.over V.left ⟶ G.over V.left) where
  toFun α := ⟨α⟩
  invFun φ := φ.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The morphism attached by `sheafHomOverEquiv` to a section `α` has underlying morphism of
presheaves of modules `α`. -/
@[simp]
lemma sheafHomOverEquiv_val (U : Opens X) (V : Over U)
    (α : ToType (((sheafHom 𝒪 h𝒪 F G).over U).val.obj (op V))) :
    (sheafHomOverEquiv 𝒪 h𝒪 F G U V α).val = α := rfl

/-- Reading the comparison at the terminal object of the slice site: the morphism attached to a
section `α` acts on sections over `V.left` by `evalSection`. -/
lemma sheafHomOverEquiv_eval (U : Opens X) (V : Over U)
    (α : ToType (((sheafHom 𝒪 h𝒪 F G).over U).val.obj (op V)))
    (x : ToType (F.val.obj (op V.left))) :
    (sheafHomOverEquiv 𝒪 h𝒪 F G U V α).val.app (op (Over.mk (𝟙 V.left))) x =
      evalSection 𝒪 F.val G.val (op V.left) α x := rfl

/-- **Evaluation of the sheaf-hom at a fixed section of `F`.** For `s` a section of `F` over
`U`, this is the morphism `SheafHom(F, G)|_U ⟶ G|_U` sending a section `α` over `V` to the
value of the corresponding morphism `F|_{V.left} ⟶ G|_{V.left}` at `s|_{V.left}`. -/
noncomputable def evalAt (U : Opens X) (s : ToType (F.val.obj (op U))) :
    (sheafHom 𝒪 h𝒪 F G).over U ⟶ G.over U where
  val :=
    { app := fun V => ModuleCat.homAddEquiv.symm
        { toFun := fun α =>
            evalSection 𝒪 F.val G.val (op V.unop.left) α (res F V.unop.hom s)
          map_add' := fun α β =>
            evalSection_add_left 𝒪 F.val G.val (op V.unop.left) α β _
          map_smul' := fun a α =>
            evalSection_smul_left 𝒪 F.val G.val (op V.unop.left) a α _ }
      naturality := fun {V V'} g => ModuleCat.hom_ext (LinearMap.ext fun α => by
        have hy : res F V'.unop.hom s = res F g.unop.left (res F V.unop.hom s) := by
          rw [res_res]
          exact congrArg (fun k : V'.unop.left ⟶ U => res F k s) (Subsingleton.elim _ _)
        change evalSection 𝒪 F.val G.val (op V'.unop.left)
            (ConcreteCategory.hom ((internalHom 𝒪 F.val G.val).map
              (Over.Hom.left g.unop).op) α) (res F V'.unop.hom s) = _
        rw [hy]
        exact evalSection_naturality 𝒪 F.val G.val (Over.Hom.left g.unop).op α
          (res F V.unop.hom s)) }

/-- On sections over `V`, `evalAt U s` evaluates a local morphism at the restriction of `s`. -/
@[simp]
lemma evalAt_val_app_apply (U : Opens X) (s : ToType (F.val.obj (op U))) (V : (Over U)ᵒᵖ)
    (α : ToType (((sheafHom 𝒪 h𝒪 F G).over U).val.obj V)) :
    (evalAt 𝒪 h𝒪 F G U s).val.app V α =
      evalSection 𝒪 F.val G.val (op V.unop.left) α (res F V.unop.hom s) := rfl

/-! ### The local kernel description of the sheaf-hom -/

/-- Sections of the structure sheaf of a ringed space commute. -/
lemma mul_comm_structureSheaf (W : Opens X)
    (b c : ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op W)))
      : b * c = c * b :=
  let : CommRing (ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj
    (op W))) :=
    inferInstanceAs (CommRing (ToType (𝒪.obj (op W))))
  mul_comm b c

/-- Evaluating a section of the internal hom at the zero section gives zero. -/
lemma evalSection_zero' (V : (Opens (X : Type u))ᵒᵖ)
    (α : ToType ((internalHom 𝒪 F.val G.val).obj V)) :
    evalSection 𝒪 F.val G.val V α 0 = 0 :=
  map_zero (α.app (op (Over.mk (𝟙 V.unop)))).hom

/-- Evaluating a section of the internal hom at a finite sum gives the sum of the evaluations. -/
lemma evalSection_sum' {ι : Type*} (V : (Opens (X : Type u))ᵒᵖ)
    (α : ToType ((internalHom 𝒪 F.val G.val).obj V)) (t : Finset ι)
    (y : ι → ToType (F.val.obj V)) :
    evalSection 𝒪 F.val G.val V α (∑ i ∈ t, y i) =
      ∑ i ∈ t, evalSection 𝒪 F.val G.val V α (y i) :=
  map_sum (α.app (op (Over.mk (𝟙 V.unop)))).hom y t

/-- **The comparison `Θ` of Stacks 01CQ.** Given finitely many sections `s` of `F` over `U`,
this is the morphism from `SheafHom(F, G)|_U` into the `s`-indexed direct sum of copies of
`G|_U` which reads off the values of a local morphism on the `s`. -/
noncomputable def sheafHomToSigma (U : Opens X) {ι : Type u} [DecidableEq ι] [Fintype ι]
    (s : ι → ToType (F.val.obj (op U))) :
    (sheafHom 𝒪 h𝒪 F G).over U ⟶ ∐ fun _ : ι => G.over U :=
  ∑ k : ι, evalAt 𝒪 h𝒪 F G U (s k) ≫ Sigma.ι (fun _ : ι => G.over U) k

/-- The `k`-th coordinate of `sheafHomToSigma` is evaluation at `s k`. -/
lemma sheafHomToSigma_comp_sigmaProj (U : Opens X) {ι : Type u} [DecidableEq ι] [Fintype ι]
    (s : ι → ToType (F.val.obj (op U))) (k : ι) :
    sheafHomToSigma 𝒪 h𝒪 F G U s ≫ sigmaProj (G.over U) k = evalAt 𝒪 h𝒪 F G U (s k) := by
  exact sum_comp_ι_comp_sigmaProj (G.over U) (fun k => evalAt 𝒪 h𝒪 F G U (s k)) k

/-- The coordinates of `Θ` are the values of the corresponding morphism on the slice site. -/
lemma sigmaProj_sheafHomToSigma_app (U : Opens X) {ι : Type u} [DecidableEq ι] [Fintype ι]
    (s : ι → ToType (F.val.obj (op U))) (V : (Over U)ᵒᵖ)
    (α : ToType (((sheafHom 𝒪 h𝒪 F G).over U).val.obj V)) (k : ι) :
    (sigmaProj (G.over U) k).val.app V ((sheafHomToSigma 𝒪 h𝒪 F G U s).val.app V α) =
      homCoords F G V.unop.hom s (sheafHomOverEquiv 𝒪 h𝒪 F G U V.unop α) k :=
  val_app_apply_congr (sheafHomToSigma_comp_sigmaProj 𝒪 h𝒪 F G U s k) V α

/-- A relation between the sections `s` makes the corresponding combination of evaluation
morphisms vanish. -/
lemma sum_evalAt_comp_smulSelf_eq_zero (U : Opens X) {ι : Type u} [Fintype ι]
    (s : ι → ToType (F.val.obj (op U)))
    (a : ι → ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
      U)))
    (ha : ∑ k : ι, a k • s k = 0) :
    ∑ k : ι, evalAt 𝒪 h𝒪 F G U (s k) ≫
      smulSelf (mul_comm_structureSheaf 𝒪 h𝒪) (a k) (G.over U) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun α => ?_))
  have hterm : ∀ k : ι,
      (evalAt 𝒪 h𝒪 F G U (s k) ≫
          smulSelf (mul_comm_structureSheaf 𝒪 h𝒪) (a k) (G.over U)).val.app V α =
        evalSection 𝒪 F.val G.val (op V.unop.left) α
          (resR (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V.unop.hom (a k) •
            res F V.unop.hom (s k)) :=
    fun k => (evalSection_smul_right 𝒪 F.val G.val (op V.unop.left) _ α _).symm
  have hsum := (evalSection_sum' 𝒪 h𝒪 F G (op V.unop.left) α Finset.univ
    (fun k : ι => resR (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V.unop.hom
      (a k) •
      res F V.unop.hom (s k))).symm
  rw [app_sum, Finset.sum_congr rfl (fun k _ => hterm k)]
  refine hsum.trans ?_
  rw [← res_sum_smul, ha, res_zero]
  exact (evalSection_zero' 𝒪 h𝒪 F G (op V.unop.left) α).trans
    (zero_app_apply (N := (sheafHom 𝒪 h𝒪 F G).over U) (P := G.over U) V α).symm

/-- **The comparison is injective on sections.** A local morphism out of `F|_{V.left}` is
determined by its values on a family of sections generating `F` there. -/
lemma sheafHomToSigma_app_injective (U : Opens X) {ι : Type u} [DecidableEq ι] [Fintype ι]
    (s : ι → ToType (F.val.obj (op U))) (V : (Over U)ᵒᵖ)
    [Epi (freeToOver F fun i => res F V.unop.hom (s i))] :
    Function.Injective ((sheafHomToSigma 𝒪 h𝒪 F G U s).val.app V) := by
  intro α α' h1
  have h2 : homCoords F G V.unop.hom s (sheafHomOverEquiv 𝒪 h𝒪 F G U V.unop α) =
      homCoords F G V.unop.hom s (sheafHomOverEquiv 𝒪 h𝒪 F G U V.unop α') :=
    funext fun k => by
      rw [← sigmaProj_sheafHomToSigma_app, ← sigmaProj_sheafHomToSigma_app, h1]
  exact (sheafHomOverEquiv 𝒪 h𝒪 F G U V.unop).injective
    (homCoords_injective F G V.unop.hom s h2)

/-- **The comparison hits every section killed by the relation matrix.** -/
lemma exists_sheafHomToSigma_app_eq (U : Opens X) {Gen Rel : Type u} [DecidableEq Gen]
    [Fintype Gen] [Fintype Rel] (s : Gen → ToType (F.val.obj (op U)))
    (rel : Rel → Gen → ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj.obj (op U)))
    (hrels : ∀ ⦃V : Opens X⦄ (f : V ⟶ U)
      (z : Gen → ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj
        (op V))),
      (∑ k : Gen, z k • res F f (s k) = 0) → ∀ y ∈ V,
      ∃ (W' : Opens X) (g : W' ⟶ V), y ∈ W' ∧
        ∃ b : Rel → ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj
          (op W')),
        ∀ k : Gen, resR (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) g (z k) =
          ∑ l : Rel, b l * resR (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) (g
            ≫ f) (rel l k))
    (V : (Over U)ᵒᵖ) [Epi (freeToOver F fun i => res F V.unop.hom (s i))]
    (z : ToType ((∐ fun _ : Gen => G.over U).val.obj V))
    (hz : ∀ l : Rel, ∑ k : Gen,
      resROver (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) V.unop (rel l k) •
        (sigmaProj (G.over U) k).val.app V z = 0) :
    ∃ α, (sheafHomToSigma 𝒪 h𝒪 F G U s).val.app V α = z := by
  classical
  obtain ⟨φ, hφ⟩ := exists_homCoords_eq F G V.unop.hom s
    (fun k => (sigmaProj (G.over U) k).val.app V z)
    (kernelι_comp_freeToOver_eq_zero F G V.unop.hom s rel hrels _ hz)
  refine ⟨(sheafHomOverEquiv 𝒪 h𝒪 F G U V.unop).symm φ, ?_⟩
  refine sigma_section_ext (G.over U) V _ _ fun k => ?_
  rw [sigmaProj_sheafHomToSigma_app, Equiv.apply_symm_apply, hφ]

/-- **Stacks 01CQ (1), with the presentation data given.** For a sheaf of modules `F` carrying
section-level finite presentation data on an open `U`, the restriction of `SheafHom(F, G)` to
`U` is the kernel of the map between finite direct sums of copies of `G|_U` given by the
relation matrix. -/
theorem nonempty_sheafHomOver_iso_kernel (x : X) (P : LocalPresentation F x)
    [DecidableEq P.Gen] [DecidableEq P.Rel] :
    Nonempty ((sheafHom 𝒪 h𝒪 F G).over P.nhd ≅
      kernel (sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd))) := by
  have hzero : sheafHomToSigma 𝒪 h𝒪 F G P.nhd P.gens ≫
      sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd) = 0 := by
    refine eq_zero_of_comp_sigmaProj _ _ fun l => ?_
    have hterm : ∀ k : P.Gen,
        sheafHomToSigma 𝒪 h𝒪 F G P.nhd P.gens ≫
            (sigmaProj (G.over P.nhd) k ≫
              smulSelf (mul_comm_structureSheaf 𝒪 h𝒪) (P.rel l k) (G.over P.nhd)) =
          evalAt 𝒪 h𝒪 F G P.nhd (P.gens k) ≫
            smulSelf (mul_comm_structureSheaf 𝒪 h𝒪) (P.rel l k) (G.over P.nhd) := by
      intro k
      rw [← Category.assoc, sheafHomToSigma_comp_sigmaProj]
    rw [Category.assoc, sigmaMatrix_comp_sigmaProj, Preadditive.comp_sum,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k),
      sum_evalAt_comp_smulSelf_eq_zero 𝒪 h𝒪 F G P.nhd P.gens (P.rel l) (P.rel_apply l)]
  have hiso : IsIso (kernel.lift (sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪)
      P.rel (G.over P.nhd)) (sheafHomToSigma 𝒪 h𝒪 F G P.nhd P.gens) hzero) := by
    refine isIso_of_bijective_app _ fun V => ?_
    have hepi : Epi (freeToOver F fun i => res F V.unop.hom (P.gens i)) := by
      refine epi_freeToOver F _ fun {V'} f t y hy => ?_
      obtain ⟨W'', g, hyW'', c, hc⟩ := P.generates (f ≫ V.unop.hom) t y hy
      refine ⟨W'', g, hyW'', c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
      rw [res_res]
      exact congrArg (fun m : W'' ⟶ P.nhd => c k • res F m (P.gens k)) (Subsingleton.elim _ _)
    exact ⟨injective_kernelLift_app _ _ hzero V
        (sheafHomToSigma_app_injective 𝒪 h𝒪 F G P.nhd P.gens V),
      surjective_kernelLift_app _ _ hzero V fun z hz =>
        exists_sheafHomToSigma_app_eq 𝒪 h𝒪 F G P.nhd P.gens P.rel P.relations V z
          (fun l => sum_resROver_smul_sigmaProj_eq_zero (mul_comm_structureSheaf 𝒪 h𝒪) P.rel
            (G.over P.nhd) V z hz l)⟩
  exact ⟨asIso (kernel.lift (sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd))
    (sheafHomToSigma 𝒪 h𝒪 F G P.nhd P.gens) hzero)⟩

/-- **The internal hom out of a finitely presented module is locally the kernel of a map
between finite direct sums of copies of the target.** -/
@[stacks 01CQ "local kernel presentation"]
theorem sheafHom_locallyKernelFiniteCoproduct [F.IsFinitePresentation] :
    ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ m n : ℕ,
      ∃ f : (∐ fun _ : Fin m => G.over U) ⟶ (∐ fun _ : Fin n => G.over U),
        Nonempty ((sheafHom 𝒪 h𝒪 F G).over U ≅ kernel f) := by
  classical
  intro x
  obtain ⟨P⟩ := nonempty_localPresentation F x
  obtain ⟨e⟩ := nonempty_sheafHomOver_iso_kernel 𝒪 h𝒪 F G x P
  let isoG : (∐ fun _ : Fin (Fintype.card P.Gen) => G.over P.nhd) ≅
      ∐ fun _ : P.Gen => G.over P.nhd :=
    Sigma.whiskerEquiv (f := fun _ : Fin (Fintype.card P.Gen) => G.over P.nhd)
      (g := fun _ : P.Gen => G.over P.nhd) (Fintype.equivFin P.Gen).symm fun _ => Iso.refl _
  let isoR : (∐ fun _ : Fin (Fintype.card P.Rel) => G.over P.nhd) ≅
      ∐ fun _ : P.Rel => G.over P.nhd :=
    Sigma.whiskerEquiv (f := fun _ : Fin (Fintype.card P.Rel) => G.over P.nhd)
      (g := fun _ : P.Rel => G.over P.nhd) (Fintype.equivFin P.Rel).symm fun _ => Iso.refl _
  refine ⟨P.nhd, P.mem_nhd, Fintype.card P.Gen, Fintype.card P.Rel,
    isoG.hom ≫ sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd) ≫ isoR.inv,
    ⟨e.trans (kernel.mapIso
      (f := isoG.hom ≫ sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd) ≫
        isoR.inv)
      (sigmaMatrix (mul_comm_structureSheaf 𝒪 h𝒪) P.rel (G.over P.nhd)) isoG isoR ?_).symm⟩⟩
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The internal hom out of a finitely presented module into a coherent module is
coherent.** -/
@[stacks 01CQ "coherence of internal Hom"]
theorem sheafHom_isCoherent [F.IsFinitePresentation] [IsCoherent G] :
    IsCoherent (sheafHom 𝒪 h𝒪 F G) :=
  isCoherent_of_locallyKernelFiniteCoproduct (sheafHom_locallyKernelFiniteCoproduct 𝒪 h𝒪 F G)

end SliceHom

end Stacks.SheafOfModules

end
