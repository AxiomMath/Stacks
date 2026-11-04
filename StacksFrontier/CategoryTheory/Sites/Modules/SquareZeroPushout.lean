module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The square-zero pushout of a presented sheaf of rings along a map out of its ideal

Let `(C, K)` be a site, let `π : R ⟶ B` be a locally surjective morphism of sheaves of
commutative rings on it, write `ℐ' = Ker π`, and let `𝒢` be a sheaf of `R`-modules on which
`ℐ'` acts by zero. Given a morphism `ψ : ℐ' ⟶ 𝒢` of `R`-modules, this file constructs the
*square-zero pushout*

`(R ⋉ 𝒢)/J`,  where  `J = {(g, -ψ g) : g ∈ ℐ'}`,

together with its projection onto `ℬ`, and proves that

`0 ⟶ 𝒢 ⟶ (R ⋉ 𝒢)/J ⟶ ℬ ⟶ 0`

is exact: the inclusion of `𝒢` is injective on sections, its image is *exactly* the kernel of
the projection on sections, and the projection is locally surjective.

This is the construction the proof of [Stacks 08UC] performs on `R = 𝒜₁[ℰ]`, the free algebra
sheaf on a family of generators of `ℬ` with coefficients in `𝒜₁`, with
`ψ = φ|_{ℐ'} + δ ∘ (ℐ' ⟶ ℐ/ℐ²)`; the map `ℐ'/(ℐ')² ⟶ ℐ/ℐ²` that the second summand uses is
`Stacks.Sites.Conormal.presentationConormalMap`.

## Main definitions

* `Stacks.Sites.SqZeroPushout.PushoutData`: the data the construction consumes — a natural
  `R`-linear family `ψ : ℐ'(U) ⟶ 𝒢(U)`, together with the fact that `ℐ'` annihilates `𝒢`.
* `Stacks.Sites.SqZeroPushout.graphSection` and `Stacks.Sites.SqZeroPushout.graphIdeal`: the
  antidiagonal section `(g, -ψ g)` and the ideal of sections it spans.
* `Stacks.Sites.SqZeroPushout.graphIdealSubsheaf`: that ideal, as a sheaf of ideals `J` of
  `R ⋉ 𝒢`.
* `Stacks.Sites.SqZeroPushout.pushoutSheaf`, `Stacks.Sites.SqZeroPushout.pushoutMk` and
  `Stacks.Sites.SqZeroPushout.pushoutProj`: the pushout `(R ⋉ 𝒢)/J`, the quotient map out of
  `R ⋉ 𝒢`, and the projection onto `ℬ`.
* `Stacks.Sites.SqZeroPushout.pushoutInr` and `Stacks.Sites.SqZeroPushout.pushoutInrHom`: the
  inclusion `n ↦ [(0, n)]` of `𝒢` into the pushout, on sections and as a homomorphism of
  additive groups of sections.

## Main results

* `Stacks.Sites.SqZeroPushout.graphIdeal`: **`J` is an ideal**, which is the one computation the
  construction rests on; see the implementation notes.
* `Stacks.Sites.SqZeroPushout.graphIdealSubsheaf`: membership in `J` is local, so `J` is a sheaf
  of ideals and the quotient `(R ⋉ 𝒢)/J` is available.
* `Stacks.Sites.SqZeroPushout.pushoutMk_comp_pushoutProj`: the projection onto `ℬ` restricted
  along the quotient map is `π` composed with the projection of the trivial extension.
* `Stacks.Sites.SqZeroPushout.isLocallySurjective_pushoutProj`: **right exactness** — the
  projection onto `ℬ` is locally surjective whenever `π` is.
* `Stacks.Sites.SqZeroPushout.pushoutInr_injective`: **left exactness** — the inclusion of `𝒢`
  is injective on sections.
* `Stacks.Sites.SqZeroPushout.pushoutProj_app_eq_zero_iff`: **exactness in the middle, with the
  kernel computed exactly** — a local section of the pushout dies in `ℬ` if and only if it is
  `[(0, n)]` for a (unique, by the previous result) local section `n` of `𝒢`.
* `Stacks.Sites.SqZeroPushout.pushoutInr_mul_pushoutInr`: the ideal `𝒢` of the pushout has
  square zero.

## Implementation notes

**Why `J` is an ideal.** For `w` a local section of `R ⋉ 𝒢` and `g` a local section of `ℐ'`,

`w · (g, -ψ g) = (w₁ g, -w₁ · ψ g + g · w₂)`,

and `g · w₂ = 0` because `g` lies in `ℐ' = Ker π` and `ℐ'` annihilates `𝒢` — that is the field
`PushoutData.smul_eq_zero`. So the product is `(w₁ g, -ψ (w₁ g))`, again a section of `J`. This
single cancellation is the whole reason the construction works, and it is why the annihilation
hypothesis is bundled with `ψ` rather than left to the consumer: without it `J` is only an
additive subsheaf. The same cancellation is what the affine model
`Stacks.Deformation.pushoutIdeal` of [Stacks 0GPW] uses, where it comes for free from `ℐ'`
being the square-zero ideal of an extension; here `ℐ'` need not be square zero, only to act as
zero on `𝒢`, which is what lets `R` be a free algebra sheaf.

**Sheafification is unavoidable.** The sectionwise quotient of `R ⋉ 𝒢` by `J` is not a sheaf:
sectionwise it is an extension of the *image presheaf* of `π` by `𝒢`, and the image presheaf is
not a sheaf unless `π` is sectionwise surjective. So `pushoutSheaf` is
`Stacks.Sites.quotientRingSheaf`, the sheafification of the sectionwise quotient, and none of
the three exactness statements is formal. Left exactness and the kernel computation are obtained
from local injectivity and local surjectivity of the sheafification unit, which is what the
hypothesis `[K.WEqualsLocallyBijective CommRingCat]` supplies; the gluing is then done by hand
against the sheaf conditions of `𝒢` and of the pushout.

**Which square-zero extension this uses.** No new trivial square-zero extension of a sheaf of
rings is introduced. The site-level one already in the library,
`Stacks.Sheaves.Differentials.sqZeroExtSheaf` of
`StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsInverseImage`, is reused unchanged, as
are the component lemmas of `PresheafOfModules.sqZeroExtPresheaf` underneath it. It already
holds at the generality needed here — an arbitrary small site and an arbitrary sheaf of
commutative rings — so no generalization was required; the two narrower copies
(`AlgebraicGeometry.SheafOfModules.sqZeroSheaf` over a topological space and
`Stacks.Smooth.sqZeroSheaf` over a scheme) are untouched.

**Spellings.** `N.val` has base `(underlyingRingSheaf R).obj`, whereas the square-zero extension
API is stated for the base `R.obj ⋙ forget₂ CommRingCat RingCat`. The two are definitionally
equal but not syntactically, which blocks `rw`; `modules` is the reducible re-ascription that
puts every statement in the second spelling, and `inrSection` plays the same role for the
pure-`𝒢` section `(0, n)`, whose `sqZeroExtMk` spelling would otherwise have to be elaborated
against a restriction of scalars at every use.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
-/

@[expose] public section

open CategoryTheory PresheafOfModules Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf sqZeroExtSheaf sqZeroExtSheafProj)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace Stacks.Sites.SqZeroPushout

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R B : Sheaf K CommRingCat.{u}} (π : R ⟶ B)
  (N : SheafOfModules.{u} (underlyingRingSheaf R))

/-- `N` read as a presheaf of modules over the presheaf `R.obj` of commutative rings: the
spelling that `PresheafOfModules.sqZeroExtPresheaf` consumes. -/
noncomputable abbrev modules :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  N.val

/-- The data out of which the square-zero pushout of `π : R ⟶ B` by a sheaf of `R`-modules `𝒢`
is built: a morphism `ψ : ℐ' ⟶ 𝒢` of `R`-modules out of the kernel ideal `ℐ' = Ker π`, given as
a natural `R`-linear family of maps on sections, together with the fact that `ℐ'` annihilates
`𝒢`.

The annihilation hypothesis is a field rather than a separate assumption because it is what
makes the graph of `ψ` an *ideal* of `R ⋉ 𝒢` and not merely an additive subsheaf; see the
implementation notes of this file. It says exactly that the `R`-module `𝒢` is a `ℬ`-module. -/
structure PushoutData where
  /-- The map `ℐ'(U) ⟶ 𝒢(U)` on sections over an object of the site. -/
  app (X : Cᵒᵖ) : ↥(kernelIdeal π.hom X) →+ ↥((modules N).obj X)
  /-- The maps on sections are `R`-linear. -/
  app_smul (X : Cᵒᵖ) (r : ↥(R.obj.obj X)) (g : ↥(kernelIdeal π.hom X)) :
    app X (r • g) = r • app X g
  /-- The maps on sections commute with the restriction maps. -/
  app_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : ↥(kernelIdeal π.hom X)) :
    app Y ⟨(R.obj.map f).hom (g : ↥(R.obj.obj X)), Conormal.map_kernel π.hom f g.2⟩ =
      (modules N).map f (app X g)
  /-- A local section of the kernel ideal `ℐ'` acts as zero on `𝒢`. -/
  smul_eq_zero (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) (m : ↥((modules N).obj X)) :
    (g : ↥(R.obj.obj X)) • m = 0

variable (ψ : PushoutData π N)

/-- The antidiagonal local section `(g, -ψ g)` of `R ⋉ 𝒢` attached to a local section `g` of
the kernel ideal `ℐ'`. These span the ideal by which the pushout is formed. -/
noncomputable def graphSection (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) :
    ↥((modules N).sqZeroExtObj X) :=
  sqZeroExtMk (g : ↥(R.obj.obj X)) (-(ψ.app X g))

/-- The first component of an antidiagonal section is the section of `ℐ'` it comes from. -/
@[simp] theorem graphSection_fst (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) :
    sqZeroExtFst (graphSection π N ψ X g) = (g : ↥(R.obj.obj X)) := by
  simp [graphSection]

/-- The second component of an antidiagonal section is minus its image under `ψ`. -/
@[simp] theorem graphSection_snd (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) :
    sqZeroExtSnd (graphSection π N ψ X g) = -(ψ.app X g) := by
  simp [graphSection]

/-- **The antidiagonal sections form an ideal `J` of `R ⋉ 𝒢`.** Multiplying `(g, -ψ g)` by a
local section `w` gives the antidiagonal section of `w₁ g`: the cross term `g · w₂` vanishes
because `g` lies in `ℐ' = Ker π` and `ℐ'` annihilates `𝒢`. -/
noncomputable def graphIdeal (X : Cᵒᵖ) : Ideal ↥((modules N).sqZeroExtObj X) where
  carrier := Set.range (graphSection π N ψ X)
  add_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
    refine ⟨g + g', sqZeroExt_ext ?_ ?_⟩
    · rw [graphSection_fst, sqZeroExtFst_add, graphSection_fst, graphSection_fst]
      rfl
    · rw [graphSection_snd, sqZeroExtSnd_add, graphSection_snd, graphSection_snd,
        map_add, neg_add]
  zero_mem' := by
    refine ⟨0, sqZeroExt_ext ?_ ?_⟩
    · rw [graphSection_fst, sqZeroExtFst_zero]; rfl
    · rw [graphSection_snd, sqZeroExtSnd_zero, map_zero, neg_zero]
  smul_mem' := by
    rintro w _ ⟨g, rfl⟩
    refine ⟨sqZeroExtFst w • g, sqZeroExt_ext ?_ ?_⟩
    · rw [smul_eq_mul, graphSection_fst, sqZeroExtFst_mul, graphSection_fst,
        Submodule.coe_smul_of_tower, smul_eq_mul]
    · rw [smul_eq_mul, graphSection_snd, sqZeroExtSnd_mul, graphSection_fst, graphSection_snd,
        ψ.smul_eq_zero X g, add_zero, ψ.app_smul, smul_neg]

/-- Membership in the ideal `J` is being an antidiagonal section. -/
theorem mem_graphIdeal_iff (X : Cᵒᵖ) (w : ↥((modules N).sqZeroExtObj X)) :
    w ∈ graphIdeal π N ψ X ↔ ∃ g : ↥(kernelIdeal π.hom X), graphSection π N ψ X g = w :=
  Iff.rfl



omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The presheaf of types underlying a sheaf of commutative rings satisfies the sheaf condition
for type-valued presheaves. -/
theorem isSheaf_forgetCommRing (O : Sheaf K CommRingCat.{u}) :
    Presieve.IsSheaf K (O.obj ⋙ forget CommRingCat.{u}) := by
  rw [← isSheaf_iff_isSheaf_of_type,
    ← Presheaf.isSheaf_iff_isSheaf_forget K _ (forget CommRingCat.{u})]
  exact O.property

omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Two sections of a type-valued sheaf which agree after restriction along every arrow of a
covering sieve are equal. -/
theorem eq_of_locally_eq {P : Cᵒᵖ ⥤ Type u} (hP : Presieve.IsSheaf K P) {X : Cᵒᵖ}
    {S : Sieve X.unop} (hS : S ∈ K X.unop) (s t : P.obj X)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → P.map f.op s = P.map f.op t) : s = t := by
  obtain ⟨u, -, hu⟩ := hP S hS (fun _ f _ => P.map f.op s)
    (fun _ _ _ g₁ g₂ f₁ f₂ _ _ hg => by
      simp only [← Functor.map_comp_apply, ← op_comp, hg])
  rw [hu s fun _ _ _ => rfl, hu t fun _ f hf => (h f hf).symm]

/-- Restriction carries the antidiagonal section of `g` to the antidiagonal section of the
restriction of `g`. -/
theorem sqZeroExtMap_graphSection {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : ↥(kernelIdeal π.hom X)) :
    ((modules N).sqZeroExtMap f).hom (graphSection π N ψ X g) =
      graphSection π N ψ Y ⟨(R.obj.map f).hom (g : ↥(R.obj.obj X)),
        Conormal.map_kernel π.hom f g.2⟩ := by
  refine sqZeroExt_ext ?_ ?_
  · rw [sqZeroExtFst_map, graphSection_fst, graphSection_fst]
  · rw [sqZeroExtSnd_map, graphSection_snd, graphSection_snd, map_neg, ψ.app_map]
    rfl

/-- The pure-`𝒢` local section `(0, n)` of the trivial square-zero extension. -/
noncomputable def inrSection (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    ↥((modules N).sqZeroExtObj X) :=
  sqZeroExtMk 0 n

/-- A pure-`𝒢` section has vanishing first component. -/
@[simp] theorem inrSection_fst (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    sqZeroExtFst (inrSection N X n) = 0 := by
  rw [inrSection, sqZeroExtFst_mk]

/-- The second component of a pure-`𝒢` section is the section of `𝒢` it comes from. -/
@[simp] theorem inrSection_snd (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    sqZeroExtSnd (inrSection N X n) = n := by
  rw [inrSection, sqZeroExtSnd_mk]

/-- The pure-`𝒢` sections are additive in the section of `𝒢`. -/
theorem inrSection_add (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) :
    inrSection N X (n + m) = inrSection N X n + inrSection N X m :=
  sqZeroExt_ext (by rw [inrSection_fst, sqZeroExtFst_add, inrSection_fst, inrSection_fst,
    add_zero]) (by rw [inrSection_snd, sqZeroExtSnd_add, inrSection_snd, inrSection_snd])

/-- The pure-`𝒢` section of the zero section is zero. -/
theorem inrSection_zero (X : Cᵒᵖ) : inrSection N X 0 = 0 :=
  sqZeroExt_ext (by rw [inrSection_fst, sqZeroExtFst_zero])
    (by rw [inrSection_snd, sqZeroExtSnd_zero])

/-- Two pure-`𝒢` sections multiply to zero in `R ⋉ 𝒢`. -/
theorem inrSection_mul_inrSection (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) :
    inrSection N X n * inrSection N X m = 0 :=
  sqZeroExt_ext
    (by rw [sqZeroExtFst_mul, inrSection_fst, sqZeroExtFst_zero, zero_mul])
    (by rw [sqZeroExtSnd_mul, inrSection_fst, inrSection_fst, zero_smul, zero_smul, add_zero,
      sqZeroExtSnd_zero])

/-- Restriction is computed componentwise on pure-`𝒢` sections. -/
theorem sqZeroExtMap_inrSection {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥((modules N).obj X)) :
    ((modules N).sqZeroExtMap f).hom (inrSection N X n) =
      inrSection N Y ((modules N).map f n) := by
  refine sqZeroExt_ext ?_ ?_
  · rw [sqZeroExtFst_map, inrSection_fst, map_zero]
    exact (inrSection_fst N Y _).symm
  · rw [sqZeroExtSnd_map, inrSection_snd]
    exact (inrSection_snd N Y _).symm

/-- Restriction carries the ideal `J` into the ideal `J` over the smaller object. -/
theorem map_mem_graphIdeal {X Y : Cᵒᵖ} (f : X ⟶ Y) {w : ↥((modules N).sqZeroExtObj X)}
    (hw : w ∈ graphIdeal π N ψ X) :
    ((modules N).sqZeroExtMap f).hom w ∈ graphIdeal π N ψ Y := by
  obtain ⟨g, rfl⟩ := hw
  exact ⟨_, (sqZeroExtMap_graphSection π N ψ f g).symm⟩


omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Naturality of `π` on sections, read as an equation between elements. -/
theorem naturality_app {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : ↥(R.obj.obj X)) :
    (B.obj.map f).hom (π.hom.app X r) = π.hom.app Y ((R.obj.map f).hom r) :=
  (NatTrans.naturality_apply π.hom f r).symm

/-- **Membership in `J` is local.** A local section of `R ⋉ 𝒢` which lies in `J` after
restriction along every arrow of a covering sieve already lies in `J`: its first component lies
in `ℐ'` because `ℬ` is a sheaf, and its second component is then minus the image of that
component under `ψ` because `𝒢` is a sheaf. -/
theorem mem_graphIdeal_of_locally_mem {X : Cᵒᵖ} (s : ↥((modules N).sqZeroExtObj X))
    {S : Sieve X.unop} (hS : S ∈ K X.unop)
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f →
      ((modules N).sqZeroExtMap f.op).hom s ∈ graphIdeal π N ψ (op Y)) :
    s ∈ graphIdeal π N ψ X := by
  have hfst : π.hom.app X (sqZeroExtFst s) = 0 := by
    refine eq_of_locally_eq (isSheaf_forgetCommRing B) hS _ _ fun Y f hf => ?_
    obtain ⟨g, hg⟩ := hs f hf
    show (B.obj.map f.op).hom (π.hom.app X (sqZeroExtFst s)) = (B.obj.map f.op).hom 0
    rw [naturality_app, map_zero, ← sqZeroExtFst_map, ← hg, graphSection_fst]
    exact g.2
  refine ⟨⟨sqZeroExtFst s, hfst⟩, sqZeroExt_ext (graphSection_fst π N ψ X _) ?_⟩
  rw [graphSection_snd, neg_eq_iff_add_eq_zero]
  refine eq_of_locally_eq (Stacks.SheafOfModules.isSheaf_forget N) hS _ _ fun Y f hf => ?_
  obtain ⟨g, hg⟩ := hs f hf
  have hg' : g = ⟨(R.obj.map f.op).hom (sqZeroExtFst s),
      Conormal.map_kernel π.hom f.op hfst⟩ := by
    refine Subtype.ext ?_
    rw [← graphSection_fst π N ψ (op Y) g, hg, sqZeroExtFst_map]
  show (modules N).map f.op ((ψ.app X) ⟨sqZeroExtFst s, hfst⟩ + sqZeroExtSnd s)
      = (modules N).map f.op 0
  rw [map_zero, map_add, ← ψ.app_map, ← sqZeroExtSnd_map, ← hg, graphSection_snd, hg']
  exact add_neg_cancel _

/-- **The graph ideal `J`, as a sheaf of ideals of `R ⋉ 𝒢`.** -/
noncomputable def graphIdealSubsheaf : Stacks.Sites.IdealSubsheaf (sqZeroExtSheaf R N) where
  obj X := graphIdeal π N ψ X
  map f _ hw := map_mem_graphIdeal π N ψ f hw
  isSheaf := fun {_} s hs => mem_graphIdeal_of_locally_mem π N ψ s hs fun _ _ hf => hf

section Quotient

variable [HasWeakSheafify K CommRingCat.{u}]

/-- **The square-zero pushout `(R ⋉ 𝒢)/J`**, a sheaf of commutative rings on the site: the
sheafification of the sectionwise quotient of the trivial square-zero extension of `R` by `𝒢`
by the graph ideal of `ψ`. -/
@[ega "0 19.5.6.1" "more general"]
noncomputable abbrev pushoutSheaf : Sheaf K CommRingCat.{u} :=
  Stacks.Sites.quotientRingSheaf (graphIdealSubsheaf π N ψ)

/-- The quotient map `R ⋉ 𝒢 ⟶ (R ⋉ 𝒢)/J`. -/
noncomputable abbrev pushoutMk : sqZeroExtSheaf R N ⟶ pushoutSheaf π N ψ :=
  Stacks.Sites.toQuotientRingSheaf (graphIdealSubsheaf π N ψ)

/-- The objectwise map `(R ⋉ 𝒢)(U)/J(U) ⟶ ℬ(U)` induced by `w ↦ π w₁`, which kills `J` because
the first component of an antidiagonal section lies in `Ker π`. -/
noncomputable def quotientToTarget :
    Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ) ⟶ B.obj where
  app X := CommRingCat.ofHom (Ideal.Quotient.lift (Stacks.Sites.sectionIdeal _ X)
    ((π.hom.app X).hom.comp ((sqZeroExtProj (modules N)).app X).hom) (by
      rintro _ ⟨g, rfl⟩
      change π.hom.app X (sqZeroExtFst (graphSection π N ψ X g)) = 0
      rw [graphSection_fst]
      exact g.2))
  naturality {X Y} f := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun w ↦ ?_))
    change π.hom.app Y (sqZeroExtFst (((modules N).sqZeroExtMap f).hom w)) =
      (B.obj.map f).hom (π.hom.app X (sqZeroExtFst w))
    rw [naturality_app]
    exact congrArg _ (sqZeroExtFst_map (M := modules N) f w)

/-- **The projection `(R ⋉ 𝒢)/J ⟶ ℬ`**, obtained from the objectwise map by the universal
property of sheafification. -/
noncomputable def pushoutProj : pushoutSheaf π N ψ ⟶ B :=
  ⟨sheafifyLift K (quotientToTarget π N ψ) B.property⟩

/-- **The pushout sits over `ℬ` compatibly with `R`.** Composing the quotient map with the
projection onto `ℬ` gives the projection of the trivial extension followed by `π`. -/
theorem pushoutMk_comp_pushoutProj :
    pushoutMk π N ψ ≫ pushoutProj π N ψ = sqZeroExtSheafProj R N ≫ π := by
  apply Sheaf.hom_ext
  show (Stacks.Sites.toQuotientPresheaf (graphIdealSubsheaf π N ψ) ≫
      toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))) ≫
      sheafifyLift K (quotientToTarget π N ψ) B.property =
    sqZeroExtProj (modules N) ≫ π.hom
  rw [Category.assoc, toSheafify_sheafifyLift]
  rfl

/-- `Stacks.Sites.SqZeroPushout.pushoutMk_comp_pushoutProj` on underlying presheaves. -/
theorem pushoutMk_comp_pushoutProj_hom :
    (pushoutMk π N ψ).hom ≫ (pushoutProj π N ψ).hom =
      sqZeroExtProj (modules N) ≫ π.hom :=
  Conormal.hom_of_comp_eq (pushoutMk_comp_pushoutProj π N ψ)

/-- The objectwise map onto `ℬ` is locally surjective when `π` is: a local section of `ℬ` that
lifts to `r` in `R` is the image of the class of `(r, 0)`. -/
instance isLocallySurjective_quotientToTarget [Presheaf.IsLocallySurjective K π.hom] :
    Presheaf.IsLocallySurjective K (quotientToTarget π N ψ) where
  imageSieve_mem {X} b := by
    refine K.superset_covering (fun Y f hf => ?_) (Presheaf.imageSieve_mem K π.hom b)
    obtain ⟨r, hr⟩ := hf
    refine ⟨Ideal.Quotient.mk _ (sqZeroExtMk (M := modules N) r
      (0 : ↥((modules N).obj (op Y)))), ?_⟩
    refine Eq.trans ?_ hr
    change π.hom.app (op Y) (sqZeroExtFst (sqZeroExtMk (M := modules N) r
      (0 : ↥((modules N).obj (op Y))))) = π.hom.app (op Y) r
    rw [sqZeroExtFst_mk]

/-- **Right exactness.** The projection `(R ⋉ 𝒢)/J ⟶ ℬ` is locally surjective whenever `π` is.
-/
theorem isLocallySurjective_pushoutProj [Presheaf.IsLocallySurjective K π.hom] :
    Presheaf.IsLocallySurjective K (pushoutProj π N ψ).hom :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac K
    (toSheafify_sheafifyLift K (quotientToTarget π N ψ) B.property)

/-- **The inclusion of `𝒢` into the pushout**, `n ↦ [(0, n)]`, on sections. -/
noncomputable def pushoutInr (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    ↥((pushoutSheaf π N ψ).obj.obj X) :=
  (pushoutMk π N ψ).hom.app X (inrSection N X n)

/-- The inclusion of `𝒢` is the sheafification unit applied to the class of `(0, n)`. -/
theorem pushoutInr_eq_toSheafify (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    pushoutInr π N ψ X n =
      (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))).app X
        (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X)
          (inrSection N X n)) :=
  rfl

/-- The inclusion of `𝒢` is additive. -/
theorem pushoutInr_add (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) :
    pushoutInr π N ψ X (n + m) = pushoutInr π N ψ X n + pushoutInr π N ψ X m := by
  show ((pushoutMk π N ψ).hom.app X).hom (inrSection N X (n + m)) = _
  rw [inrSection_add]
  exact map_add ((pushoutMk π N ψ).hom.app X).hom _ _

/-- The inclusion of `𝒢` sends zero to zero. -/
theorem pushoutInr_zero (X : Cᵒᵖ) : pushoutInr π N ψ X 0 = 0 := by
  show ((pushoutMk π N ψ).hom.app X).hom (inrSection N X 0) = _
  rw [inrSection_zero]
  exact map_zero ((pushoutMk π N ψ).hom.app X).hom

/-- The inclusion of `𝒢` commutes with the restriction maps. -/
theorem pushoutInr_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥((modules N).obj X)) :
    ((pushoutSheaf π N ψ).obj.map f).hom (pushoutInr π N ψ X n) =
      pushoutInr π N ψ Y ((modules N).map f n) := by
  show ((pushoutSheaf π N ψ).obj.map f).hom
    ((pushoutMk π N ψ).hom.app X (inrSection N X n)) = _
  rw [← NatTrans.naturality_apply (pushoutMk π N ψ).hom f (inrSection N X n)]
  show ((pushoutMk π N ψ).hom.app Y).hom (((modules N).sqZeroExtMap f).hom
    (inrSection N X n)) = _
  rw [sqZeroExtMap_inrSection]
  rfl

/-- **The ideal `𝒢` of the pushout has square zero.** -/
theorem pushoutInr_mul_pushoutInr (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) :
    pushoutInr π N ψ X n * pushoutInr π N ψ X m = 0 := by
  calc pushoutInr π N ψ X n * pushoutInr π N ψ X m
      = ((pushoutMk π N ψ).hom.app X).hom (inrSection N X n * inrSection N X m) :=
        (map_mul ((pushoutMk π N ψ).hom.app X).hom _ _).symm
    _ = 0 := by
        rw [inrSection_mul_inrSection]
        exact map_zero ((pushoutMk π N ψ).hom.app X).hom

/-- **The image of `𝒢` is an ideal of the pushout, acted on through `ℬ`.** The class of a local
section `w` of `R ⋉ 𝒢` multiplies `[(0, n)]` to `[(0, w₁ n)]`, where `w₁` is the first component
of `w`; as `w₁` and the image of `[w]` in `ℬ` correspond under `π`, this is the action of `ℬ`. -/
theorem pushoutMk_mul_pushoutInr (X : Cᵒᵖ) (w : ↥((modules N).sqZeroExtObj X))
    (n : ↥((modules N).obj X)) :
    (pushoutMk π N ψ).hom.app X w * pushoutInr π N ψ X n =
      pushoutInr π N ψ X (sqZeroExtFst w • n) := by
  calc (pushoutMk π N ψ).hom.app X w * pushoutInr π N ψ X n
      = ((pushoutMk π N ψ).hom.app X).hom (w * inrSection N X n) :=
        (map_mul ((pushoutMk π N ψ).hom.app X).hom _ _).symm
    _ = pushoutInr π N ψ X (sqZeroExtFst w • n) :=
        congrArg ((pushoutMk π N ψ).hom.app X).hom <|
          sqZeroExt_ext (by simp only [sqZeroExtFst_mul, inrSection_fst, mul_zero])
            (by simp only [sqZeroExtSnd_mul, inrSection_fst, inrSection_snd, zero_smul, add_zero])

/-- The composite `𝒢 ⟶ (R ⋉ 𝒢)/J ⟶ ℬ` is zero. -/
theorem pushoutProj_pushoutInr (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    (pushoutProj π N ψ).hom.app X (pushoutInr π N ψ X n) = 0 := by
  show ((pushoutMk π N ψ).hom.app X ≫ (pushoutProj π N ψ).hom.app X) (inrSection N X n) = 0
  rw [← NatTrans.comp_app, pushoutMk_comp_pushoutProj_hom]
  show π.hom.app X (sqZeroExtFst (inrSection N X n)) = 0
  rw [inrSection_fst, map_zero]

/-- The inclusion of `𝒢` into the pushout, as a homomorphism of the additive groups of local
sections. -/
noncomputable def pushoutInrHom (X : Cᵒᵖ) :
    ↥((modules N).obj X) →+ ↥((pushoutSheaf π N ψ).obj.obj X) where
  toFun := pushoutInr π N ψ X
  map_zero' := pushoutInr_zero π N ψ X
  map_add' := pushoutInr_add π N ψ X

section Exact

variable [K.WEqualsLocallyBijective CommRingCat.{u}]

omit [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}] in
/-- A local section of `𝒢` vanishing after restriction along every arrow of a covering sieve is
zero. -/
theorem eq_zero_of_locally_zero {X : Cᵒᵖ} {S : Sieve X.unop} (hS : S ∈ K X.unop)
    (n : ↥((modules N).obj X))
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → (modules N).map f.op n = 0) : n = 0 := by
  refine eq_of_locally_eq (Stacks.SheafOfModules.isSheaf_forget N) hS n 0 fun Y f hf => ?_
  have h1 : ((N.val.presheaf ⋙ forget AddCommGrpCat.{u}).map f.op) n = 0 := h f hf
  rw [h1]
  exact (map_zero (ConcreteCategory.hom (N.val.presheaf.map f.op))).symm

/-- A local section of `𝒢` whose image in the pushout vanishes is zero: locally its class
`[(0, n)]` is antidiagonal, and an antidiagonal section with vanishing first component is zero,
so `n` vanishes locally and hence vanishes. -/
theorem eq_zero_of_pushoutInr_eq_zero {X : Cᵒᵖ} {n : ↥((modules N).obj X)}
    (h : pushoutInr π N ψ X n = 0) : n = 0 := by
  have hS := Presheaf.equalizerSieve_mem K
    (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ)))
    (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X)
      (inrSection N X n)) 0
    (h.trans (map_zero
      (((toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))).app X).hom)).symm)
  refine eq_zero_of_locally_zero N hS n fun Y f hf => ?_
  have hf' : Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) (op Y))
      (((modules N).sqZeroExtMap f.op).hom (inrSection N X n)) = 0 := by
    refine hf.trans ?_
    exact map_zero ((Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ)).map f.op).hom
  rw [sqZeroExtMap_inrSection] at hf'
  have key : ∀ m : ↥((modules N).obj (op Y)),
      (∃ g : ↥(kernelIdeal π.hom (op Y)),
        graphSection π N ψ (op Y) g = inrSection N (op Y) m) → m = 0 := by
    rintro m ⟨g, hg⟩
    have hg0 : g = 0 := Subtype.ext (by
      rw [← graphSection_fst π N ψ (op Y) g, hg, inrSection_fst]
      rfl)
    rw [← inrSection_snd N (op Y) m, ← hg, graphSection_snd, hg0, map_zero, neg_zero]
  exact key _ (Ideal.Quotient.eq_zero_iff_mem.1 hf')

/-- **Left exactness.** The inclusion of `𝒢` into the pushout is injective on sections. -/
theorem pushoutInr_injective (X : Cᵒᵖ) : Function.Injective (pushoutInr π N ψ X) :=
  (injective_iff_map_eq_zero (pushoutInrHom π N ψ X)).2
    fun _ h => eq_zero_of_pushoutInr_eq_zero π N ψ h

/-- A local section of the pushout which lies in the image of `𝒢` after restriction along every
arrow of a covering sieve lies in that image: the local preimages are unique, hence agree on
overlaps, hence glue in `𝒢`, and the pushout is a sheaf. -/
theorem exists_pushoutInr_of_locally {X : Cᵒᵖ}
    (s : ↥((pushoutSheaf π N ψ).obj.obj X)) {S : Sieve X.unop} (hS : S ∈ K X.unop)
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → ∃ n : ↥((modules N).obj (op Y)),
      pushoutInr π N ψ (op Y) n = ((pushoutSheaf π N ψ).obj.map f.op).hom s) :
    ∃ n : ↥((modules N).obj X), pushoutInr π N ψ X n = s := by
  classical
  obtain ⟨t, ht, -⟩ := Stacks.SheafOfModules.isSheaf_forget N S hS
    (fun _ f hf => (hs f hf).choose) (by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
      have e : ∀ {Y : C} (g : Z ⟶ Y) (f : Y ⟶ X.unop) (h : S f),
          pushoutInr π N ψ (op Z) ((modules N).map g.op (hs f h).choose) =
            ((pushoutSheaf π N ψ).obj.map g.op).hom
              (((pushoutSheaf π N ψ).obj.map f.op).hom s) := fun g f h => by
        rw [← pushoutInr_map, (hs f h).choose_spec]
      have hmaps : ((pushoutSheaf π N ψ).obj.map g₁.op).hom
            (((pushoutSheaf π N ψ).obj.map f₁.op).hom s)
          = ((pushoutSheaf π N ψ).obj.map g₂.op).hom
              (((pushoutSheaf π N ψ).obj.map f₂.op).hom s) := by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg]
      exact pushoutInr_injective π N ψ (op Z) ((e g₁ f₁ h₁).trans (hmaps.trans (e g₂ f₂ h₂).symm)))
  refine ⟨t, ?_⟩
  refine eq_of_locally_eq (isSheaf_forgetCommRing (pushoutSheaf π N ψ)) hS _ _ fun Y f hf => ?_
  exact (pushoutInr_map π N ψ f.op t).trans
    ((congrArg (pushoutInr π N ψ (op Y)) (ht f hf)).trans (hs f hf).choose_spec)

/-- **Exactness in the middle, with the kernel computed exactly.** A local section of the
pushout dies in `ℬ` if and only if it is `[(0, n)]` for a local section `n` of `𝒢`.

One inclusion is `pushoutProj_pushoutInr`. For the other, a local section of the pushout lifts,
locally, to a class `[w]` of a section of `R ⋉ 𝒢`; dying in `ℬ` forces `w₁` to lie in `ℐ'`, and
then `[w] = [(0, w₂ + ψ w₁)]` because `w - (0, w₂ + ψ w₁)` is the antidiagonal section of `w₁`.
The local sections of `𝒢` so produced are unique by `pushoutInr_injective`, hence glue. -/
theorem pushoutProj_app_eq_zero_iff (X : Cᵒᵖ)
    (s : ↥((pushoutSheaf π N ψ).obj.obj X)) :
    (pushoutProj π N ψ).hom.app X s = 0 ↔
      ∃ n : ↥((modules N).obj X), pushoutInr π N ψ X n = s := by
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => hn ▸ pushoutProj_pushoutInr π N ψ X n⟩
  refine exists_pushoutInr_of_locally π N ψ s
    (Presheaf.imageSieve_mem K
      (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))) s)
    fun Y f hf => ?_
  obtain ⟨t, hts⟩ := hf
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hw : π.hom.app (op Y) (sqZeroExtFst w) = 0 := by
    have e1 : (quotientToTarget π N ψ).app (op Y)
        (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) (op Y)) w) =
        (pushoutProj π N ψ).hom.app (op Y)
          ((toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))).app (op Y)
            (Ideal.Quotient.mk _ w)) :=
      (congrArg (fun α : Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ) ⟶ B.obj =>
        α.app (op Y) (Ideal.Quotient.mk _ w))
        (toSheafify_sheafifyLift K (quotientToTarget π N ψ) B.property)).symm
    have e2 : (pushoutProj π N ψ).hom.app (op Y)
        (((pushoutSheaf π N ψ).obj.map f.op).hom s)
        = (B.obj.map f.op).hom ((pushoutProj π N ψ).hom.app X s) :=
      NatTrans.naturality_apply (pushoutProj π N ψ).hom f.op s
    rw [hts] at e1
    refine e1.trans (e2.trans ?_)
    rw [h, map_zero]
  refine ⟨sqZeroExtSnd w + ψ.app (op Y) ⟨sqZeroExtFst w, hw⟩, ?_⟩
  refine Eq.trans ?_ hts
  have hwe : inrSection N (op Y) (sqZeroExtSnd w + ψ.app (op Y) ⟨sqZeroExtFst w, hw⟩) +
      graphSection π N ψ (op Y) ⟨sqZeroExtFst w, hw⟩ = w :=
    sqZeroExt_ext (by rw [sqZeroExtFst_add, inrSection_fst, graphSection_fst, zero_add])
      (by rw [sqZeroExtSnd_add, inrSection_snd, graphSection_snd]; abel)
  refine (pushoutInr_eq_toSheafify π N ψ _ _).trans (congrArg _ (Ideal.Quotient.eq.2 ?_).symm)
  exact ⟨_, (sub_eq_of_eq_add' hwe.symm).symm⟩

end Exact

end Quotient

end Stacks.Sites.SqZeroPushout
