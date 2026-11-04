module

public import StacksFrontier.Algebra.MittagLeffler.Criteria
public import StacksFrontier.RingTheory.Module.DirectLimit.Countable
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.Algebra.MittagLeffler.Descent

@[expose] public section

universe u v

/-!
# Flat countably generated Mittag-Leffler modules are projective

Let `R` be a commutative ring and `M` a flat, countably generated, Mittag-Leffler `R`-module.
Then `M` is projective (Stacks 059X).

The argument is the source's. Every `R`-module is the colimit of a directed system of finitely
presented modules; when `M` is Mittag-Leffler that system may, by Stacks 059W, be replaced by a
subsystem indexed by a countable directed set, and the dual systems `Hom_R(M i, N)` are then
Mittag-Leffler inverse systems by Stacks 059E. Choosing a surjection `p : L → M` from a free
module `L` with kernel `K`, the sequences `0 → Hom(M i, K) → Hom(M i, L) → Hom(M i, M) → 0` are
exact — surjectivity is where flatness enters, a map from a finitely presented module to a flat
module factoring through a finite free module — so Stacks 0598 makes
`lim_i Hom(M i, L) → lim_i Hom(M i, M)` surjective. The canonical family `(M i → M)` is an
element of the target, and a preimage is a compatible family `M i → L` splitting `p` in the
colimit; hence `M` is a direct summand of `L`, so projective.

## Main results

* `Stacks.MittagLeffler.FlatIsProjective.solution`: the statement of Stacks 059X.

## Implementation notes

Rather than Lazard's theorem (Stacks 058G), which produces a system of finite *free* modules, the
route here uses the elementary fact that every module is a directed colimit of finitely presented
modules (`Stacks.MittagLeffler.FlatIsProjective.exists_isColimit_finitePresentation_system`) and
puts flatness to work only where it is needed, in the surjectivity of `Hom(M i, L) → Hom(M i, M)`;
that surjectivity is Mathlib's `Module.Flat.exists_factorization_of_finitePresentation`, which is
Stacks 058E. This avoids the universe restriction of the repository's form of Lazard's theorem,
whose module and ring share a universe, whereas here `R : Type u` and `M : Type v` with
`Small.{v} R`.

The free cover of `M` is `M →₀ Shrink.{v} R`, the free module on the underlying set of `M` with
its scalars transported into `Type v`; this keeps every module in the argument an object of
`ModuleCat.{v} R`, as Stacks 059E requires of its test modules.

Stacks 059A states the Mittag-Leffler condition categorically, as
`(F.op ⋙ yoneda.obj N).IsMittagLeffler` for the `N`-valued dual diagram, while Stacks 0598 asks for
it elementwise, on a family of abelian groups with transition homomorphisms. The two are translated
by `Stacks.MittagLeffler.FlatIsProjective.isMittagLefflerSystem_dualTrans`: the dual systems are
built here as `dualTrans` and `dualMor`, `Hom_R(F i, X)` with precomposition by `F.map` and
postcomposition by a map of coefficients, and
`Stacks.MittagLeffler.FlatIsProjective.range_dualTrans` identifies the images of the two transition
maps. The elementwise form quantifies over `k ≥ j` and asks for equality of images where the
categorical form quantifies over all `k` and asks for containment; over a directed index the two
agree, the missing containment being automatic from `dualTrans_trans`.

## References

* [Stacks project, Tag 059X](https://stacks.math.columbia.edu/tag/059X)
-/


open CategoryTheory Limits

namespace Stacks.MittagLeffler.FlatIsProjective

open Stacks.MittagLeffler.PresentingSystem

variable {R : Type u} [CommRing R] [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M]

attribute [local simp] freeProj_single

private theorem freeProj_surjective : Function.Surjective (freeProj R M) := fun x ↦
  ⟨Finsupp.single x ((Shrink.linearEquiv R R).symm 1), by simp⟩

section System

variable (R M)

-- The index set of the presenting system is a product of preorders; its category structure must
-- be the one coming from that preorder, not the product of the two categories.
attribute [-instance] CategoryTheory.uniformProd CategoryTheory.prod' CategoryTheory.prod

attribute [local simp] trans_mk

private theorem directedSystem_trans :
    DirectedSystem (sys R M) fun i j h ↦ (trans R M i j h : _ → _) where
  map_self i x := by
    obtain ⟨y, rfl⟩ := (rels R M i).mkQ_surjective x
    exact congrArg _ (Subtype.ext rfl)
  map_map {i j k} hij hjk x := by
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg _ (Subtype.ext rfl)

attribute [local simp] toM_mk

/-- Every `R`-module is the colimit of a directed system of finitely presented `R`-modules. -/
private theorem exists_isColimit_finitePresentation_system :
    ∃ (J : Type v) (_ : Preorder J) (_ : IsDirectedOrder J) (_ : Nonempty J)
      (F : J ⥤ ModuleCat.{v} R) (_ : ∀ i, Module.FinitePresentation R (F.obj i))
      (ι : F ⟶ (Functor.const J).obj (ModuleCat.of R M)),
      Nonempty (IsColimit (Cocone.mk (ModuleCat.of R M) ι)) := by
  classical
  have : DecidableEq (Idx R M) := Classical.decEq _
  have := directedSystem_trans R M
  have key : ∀ ψ : Module.DirectLimit (sys R M) (trans R M) →ₗ[R] M,
      (∀ z, ψ z = 0 → z = 0) → Function.Injective ψ := fun ψ h a b hab ↦
    eq_of_sub_eq_zero <| h (a - b) <| by rw [map_sub, hab, sub_self]
  set φ : Module.DirectLimit (sys R M) (trans R M) →ₗ[R] M :=
    Module.DirectLimit.lift R (Idx R M) (sys R M) (trans R M) (toM R M)
      (toM_trans R M) with hφ
  have hsurj : Function.Surjective φ := by
    intro x
    refine ⟨Module.DirectLimit.of R _ _ _ (({x} : Finset M), (∅ : Finset (M →₀ Shrink.{v} R)))
      (Submodule.Quotient.mk ⟨Finsupp.single x ((Shrink.linearEquiv R R).symm 1),
        Finsupp.single_mem_supported R _ (by simp)⟩), ?_⟩
    rw [hφ, Module.DirectLimit.lift_of, toM_mk]
    simp
  have hzero : ∀ z : Module.DirectLimit (sys R M) (trans R M), φ z = 0 → z = 0 := by
    intro z hz
    obtain ⟨i, w, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨y, rfl⟩ := (rels R M i).mkQ_surjective w
    rw [Submodule.mkQ_apply] at hz ⊢
    rw [hφ, Module.DirectLimit.lift_of] at hz
    set j : Idx R M := (i.1, insert (↑y : M →₀ Shrink.{v} R) i.2)
    have hij : i ≤ j := ⟨le_rfl, Finset.subset_insert _ _⟩
    have hzz : trans R M i j hij (Submodule.Quotient.mk y) = 0 := by
      rw [trans_mk]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.subset_span ⟨Finset.mem_insert_self _ _, hz⟩)
    rw [← Module.DirectLimit.of_f (hij := hij), hzz, map_zero]
  refine ⟨Idx R M, inferInstance, ⟨fun a b ↦ ⟨(a.1 ∪ b.1, a.2 ∪ b.2),
      ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
      ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩⟩, inferInstance,
    ModuleCat.directLimitDiagram (sys R M) (trans R M),
    fun i ↦ Stacks.MittagLeffler.FlatDescent.finitePresentation_sys R M i,
    { app := fun i ↦ ModuleCat.ofHom (toM R M i)
      naturality := fun i j h ↦ by
        ext y
        exact toM_trans R M i j h.le y }, ⟨?_⟩⟩
  refine IsColimit.ofIsoColimit (ModuleCat.directLimitIsColimit (sys R M) (trans R M))
    (Cocone.ext (LinearEquiv.toModuleIso (LinearEquiv.ofBijective φ ⟨key φ hzero, hsurj⟩)) ?_)
  intro i
  ext y
  exact Module.DirectLimit.lift_of (f := trans R M) (g := toM R M)
    (Hg := toM_trans R M) (x := y)

end System

section Engine

variable {J : Type v} [Preorder J] (F : J ⥤ ModuleCat.{v} R) (X : Type v) [AddCommGroup X]
  [Module R X]

omit [Small.{v} R]

/-- The transition maps of the `X`-valued dual of a directed system `F` of `R`-modules: the map
attached to `i ≤ j` is precomposition with `F.map`, `Hom_R(F j, X) → Hom_R(F i, X)`. -/
private noncomputable def dualTrans ⦃i j : J⦄ (h : i ≤ j) :
    (F.obj j →ₗ[R] X) →+ (F.obj i →ₗ[R] X) :=
  (LinearMap.lcomp R X (F.map (homOfLE h)).hom).toAddMonoidHom

private theorem dualTrans_apply ⦃i j : J⦄ (h : i ≤ j) (u : F.obj j →ₗ[R] X) :
    dualTrans F X h u = u ∘ₗ (F.map (homOfLE h)).hom := rfl

private theorem dualTrans_trans ⦃i j k : J⦄ (hij : i ≤ j) (hjk : j ≤ k) (u : F.obj k →ₗ[R] X) :
    dualTrans F X hij (dualTrans F X hjk u) = dualTrans F X (hij.trans hjk) u := by
  ext x
  simp [dualTrans_apply, ← ModuleCat.comp_apply, ← F.map_comp, homOfLE_comp]

private theorem inverseSystem_dualTrans :
    InverseSystem fun ⦃i j : J⦄ (h : i ≤ j) ↦ (dualTrans F X h : _ → _) where
  map_self i u := by
    ext x
    simp [dualTrans_apply]
  map_map _ _ _ hkj hji u := dualTrans_trans F X hkj hji u

private theorem range_dualTrans ⦃i j : J⦄ (h : i ≤ j) :
    Set.range (dualTrans F X h) = ModuleCat.Hom.hom ''
      Set.range ((F.op ⋙ yoneda.obj (ModuleCat.of R X)).map (homOfLE h).op) := by
  ext u
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, ⟨ModuleCat.ofHom t, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨w, rfl⟩, rfl⟩
    exact ⟨w.hom, rfl⟩

/-- The Mittag-Leffler condition on the dual system `Hom_R(F i, X)`, in the elementwise form
Stacks 0598 asks for, from the categorical form of Stacks 059A. -/
private theorem isMittagLefflerSystem_dualTrans
    (hF : (F.op ⋙ yoneda.obj (ModuleCat.of R X)).IsMittagLeffler) :
    IsMittagLefflerSystem (fun i ↦ F.obj i →ₗ[R] X) (dualTrans F X) := by
  intro i
  obtain ⟨jo, w, hw⟩ := hF (Opposite.op i)
  refine ⟨jo.unop, w.unop.le, fun {k} hjk ↦ Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨dualTrans F X hjk t, dualTrans_trans F X _ hjk t⟩
  · rw [range_dualTrans, range_dualTrans]
    exact Set.image_mono (hw (homOfLE (w.unop.le.trans hjk)).op)

variable {X} {Y : Type v} [AddCommGroup Y] [Module R Y]

/-- Postcomposition with `t : X → Y`, as a morphism from the `X`-valued dual system of `F` to its
`Y`-valued one. -/
private noncomputable def dualMor (t : X →ₗ[R] Y) ⦃i : J⦄ :
    (F.obj i →ₗ[R] X) →+ (F.obj i →ₗ[R] Y) :=
  (LinearMap.compRight R t).toAddMonoidHom

private theorem dualMor_apply (t : X →ₗ[R] Y) ⦃i : J⦄ (u : F.obj i →ₗ[R] X) :
    dualMor F t u = t ∘ₗ u := rfl

private theorem isInverseSystemMorphism_dualMor (t : X →ₗ[R] Y) :
    IsInverseSystemMorphism _ (dualTrans F X) _ (dualTrans F Y) (dualMor F t) := by
  intro i j h
  ext u x
  rfl

private theorem injective_dualMor {t : X →ₗ[R] Y} (ht : Function.Injective t) (i : J) :
    Function.Injective (dualMor F t (i := i)) := by
  intro u u' huu'
  ext x
  exact ht (LinearMap.congr_fun huu' x)

/-- Dualizing a surjection `p : L → N` onto a flat module against a directed system of finitely
presented modules gives a short exact sequence of inverse systems. Surjectivity of
`Hom_R(F i, L) → Hom_R(F i, N)` is where flatness enters: a map from a finitely presented module
to a flat module factors through a finite free module, which lifts along `p`. -/
private theorem isExactSeq_dual {L N : Type v} [AddCommGroup L] [Module R L] [AddCommGroup N]
    [Module R N] [Module.Flat R N] [∀ i, Module.FinitePresentation R (F.obj i)]
    {p : L →ₗ[R] N} (hp : Function.Surjective p) :
    IsExactSeq (φ := dualTrans F ↥(LinearMap.ker p)) (ψ := dualTrans F L)
      (χ := dualTrans F N) (dualMor F (LinearMap.ker p).subtype) (dualMor F p) where
  hf_mor := isInverseSystemMorphism_dualMor F _
  hg_mor := isInverseSystemMorphism_dualMor F _
  hf_inj i := injective_dualMor F Subtype.val_injective i
  h_exact i := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨u, rfl⟩
      ext x
      simp [dualMor_apply]
    · intro hv
      refine ⟨LinearMap.codRestrict _ v fun x ↦ ?_, rfl⟩
      simpa [dualMor_apply] using LinearMap.congr_fun hv x
  hg_surj := fun i w ↦ by
    obtain ⟨k, h₂, h₃, hw⟩ := Module.Flat.exists_factorization_of_finitePresentation w
    obtain ⟨t, ht⟩ := Module.projective_lifting_property p h₃ hp
    exact ⟨t ∘ₗ h₂, by rw [dualMor_apply, ← LinearMap.comp_assoc, ht, hw]⟩

end Engine

/-- The engine of Stacks 059X: if a flat module is the colimit of a Mittag-Leffler system of
finitely presented modules indexed by a countable directed set, it is projective.

Let `p : L → c.pt` be the free cover `freeProj R c.pt` and `K = Ker p`. Dualizing into `K`, `L`
and `c.pt` gives three inverse systems over `J`, `A i = Hom(F.obj i, K)`, `B i = Hom(F.obj i, L)`,
`C i = Hom(F.obj i, c.pt)`, with transition maps precomposition by `F.map`; `IsExactSeq` holds
for postcomposition with `K.subtype` and with `p`, its surjectivity part being exactly
`Module.Flat.exists_factorization_of_finitePresentation` (a map from a finitely presented module to
a flat module factors through a finite free one, which lifts along `p`), and `A` is Mittag-Leffler
by `hMLsys` at `N = K`. So `invLimit_map_surjective` (Stacks 0598) applies, and the canonical
family `(c.ι.app i)` in `lim C` has a preimage in `lim B`: a compatible family `F.obj i → L` whose
`hc.desc` splits `p`. -/
private theorem projective_of_isColimit {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    [Countable J] {F : J ⥤ ModuleCat.{v} R} {c : Cocone F} (hc : IsColimit c)
    (hMLsys : F.IsMittagLefflerSystem) [Module.Flat R (c.pt : Type v)] :
    Module.Projective R (c.pt : Type v) := by
  have := hMLsys.1
  have : Module.Projective R ((c.pt : Type v) →₀ Shrink.{v} R) :=
    Module.Projective.of_equiv (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R).symm)
  obtain ⟨p, hp⟩ : ∃ p : ((c.pt : Type v) →₀ Shrink.{v} R) →ₗ[R] (c.pt : Type v),
      Function.Surjective p := ⟨freeProj R (c.pt : Type v), freeProj_surjective⟩
  -- the canonical family `(c.ι.app i)` is an element of `lim_i Hom_R(F i, c.pt)`
  have hγ : (fun i ↦ (c.ι.app i).hom) ∈
      addInvLimit (fun i ↦ F.obj i →ₗ[R] (c.pt : Type v)) (dualTrans F (c.pt : Type v)) := by
    intro i j h
    ext x
    simp [dualTrans_apply]
  -- Stacks 0598 applied to the dual systems of `0 → Ker p → L → c.pt → 0`
  obtain ⟨b, hb⟩ := invLimit_map_surjective
    (inverseSystem_dualTrans F ↥(LinearMap.ker p))
    (inverseSystem_dualTrans F ((c.pt : Type v) →₀ Shrink.{v} R))
    (inverseSystem_dualTrans F (c.pt : Type v)) (isExactSeq_dual F hp)
    (isMittagLefflerSystem_dualTrans F ↥(LinearMap.ker p)
      (hMLsys.2 (ModuleCat.of R ↥(LinearMap.ker p)))) ⟨_, hγ⟩
  have hbi : ∀ i, p ∘ₗ b.1 i = (c.ι.app i).hom := fun i ↦ congrFun (Subtype.ext_iff.mp hb) i
  -- the compatible family `b` is a cocone on `F`, so it factors through the colimit
  have hnat : ∀ ⦃i j : J⦄ (h : i ⟶ j), F.map h ≫ ModuleCat.ofHom (b.1 j) =
      ModuleCat.ofHom (b.1 i) ≫ ((Functor.const J).obj
        (ModuleCat.of R ((c.pt : Type v) →₀ Shrink.{v} R))).map h := by
    intro i j h
    have hcompat : b.1 j ∘ₗ (F.map h).hom = b.1 i := b.property h.le
    exact ModuleCat.hom_ext (by simpa using hcompat)
  obtain ⟨s, hs⟩ : ∃ s : c.pt ⟶ ModuleCat.of R ((c.pt : Type v) →₀ Shrink.{v} R),
      ∀ i, c.ι.app i ≫ s = ModuleCat.ofHom (b.1 i) :=
    ⟨hc.desc (Cocone.mk _ ⟨fun i ↦ ModuleCat.ofHom (b.1 i), hnat⟩), hc.fac _⟩
  have hsplit : s ≫ ModuleCat.ofHom p = 𝟙 c.pt := by
    refine hc.hom_ext fun i ↦ ?_
    rw [← Category.assoc, hs i, Category.comp_id, ← ModuleCat.ofHom_comp, hbi i,
      ModuleCat.ofHom_hom]
  exact Module.Projective.of_split s.hom p (by simpa using congrArg ModuleCat.Hom.hom hsplit)

/-- Stacks 059X, with the Mittag-Leffler condition written out in the intrinsic form 059E (1)
and countable generation as a countable spanning set: a flat, countably generated,
Mittag-Leffler module over a commutative ring is projective. -/
public theorem solution (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Flat R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    Module.Projective R M := by
  obtain ⟨J, hpre, hdir, hne, F, hfp, ι, ⟨hc⟩⟩ :=
    exists_isColimit_finitePresentation_system (R := R) (M := M)
  set c : Cocone F := Cocone.mk (ModuleCat.of R M) ι
  -- condition (1) of Stacks 059E, transcribed from `hML`
  have hone : ∀ (P : ModuleCat.{v} R) [Module.FinitePresentation R P] (f : P ⟶ c.pt),
      ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q) (g : P ⟶ Q),
        ∀ T : ModuleCat.{v} R,
          LinearMap.ker (f.hom.rTensor T) = LinearMap.ker (g.hom.rTensor T) := by
    intro P _ f
    obtain ⟨Q, _, _, _, g, hg⟩ := hML P f.hom
    exact ⟨ModuleCat.of R Q, ‹_›, ModuleCat.ofHom g, fun T ↦ hg T⟩
  -- condition (3): the system factors eventually
  have hfac := ((F.tfae_isMittagLefflerSystem hc).out 1 3).mp hone
  -- Stacks 059W: shrink the index set to a countable directed subset
  obtain ⟨s, hsne, hscount, hsdir, ⟨hc'⟩⟩ :=
    ModuleCat.exists_countable_directedOn_isColimit_whisker hfac hc hcg
  have : Nonempty (↥s) := hsne.to_subtype
  have : Countable (↥s) := hscount.to_subtype
  have : IsDirectedOrder (↥s) := ⟨fun a b ↦ by
    obtain ⟨k, hk, hak, hbk⟩ := hsdir a a.2 b b.2
    exact ⟨⟨k, hk⟩, hak, hbk⟩⟩
  set F' : ↥s ⥤ ModuleCat.{v} R := (Set.mono_coe s).functor ⋙ F
  have : ∀ i, Module.FinitePresentation R (F'.obj i) := fun i ↦ hfp _
  have hMLsys := ((F'.tfae_isMittagLefflerSystem hc').out 1 4).mp hone
  have : Module.Flat R ((c.whisker (Set.mono_coe s).functor).pt : Type v) :=
    ‹Module.Flat R M›
  exact projective_of_isColimit hc' hMLsys

end Stacks.MittagLeffler.FlatIsProjective

/-!
# Flat countably generated Mittag-Leffler modules are projective

Let `R` be a commutative ring and let `M` be an `R`-module which is flat, Mittag-Leffler and
countably generated. Then `M` is projective (Stacks 059X). This is the key step towards the
characterization of projective modules as the flat Mittag-Leffler modules that are direct sums of
countably generated ones (Stacks 059Z), which follows from it by Kaplansky's theorem together with
the stability of flatness and of the Mittag-Leffler property under passing to direct summands.

By Lazard's theorem (Stacks 058G) flatness lets one write `M = colim_{i ∈ I} M i` as a directed
colimit of finite free `R`-modules, and countable generation lets one shrink `I` to a countable
directed index set (Stacks 059W). Given a short exact sequence `0 → N₁ → N₂ → N₃ → 0`, each
`0 → Hom(M i, N₁) → Hom(M i, N₂) → Hom(M i, N₃) → 0` is exact because `M i` is finite free, and the
inverse system `(Hom(M i, N₁))` over the countable directed set `I` is Mittag-Leffler because `M`
is; so taking limits preserves exactness (Stacks 0598), and `Hom(M, N) ≅ lim_i Hom(M i, N)`
functorially in `N` turns this into exactness of `0 → Hom(M, N₁) → Hom(M, N₂) → Hom(M, N₃) → 0`,
which is projectivity of `M`.

Both converses hold: a projective module is flat and Mittag-Leffler (Stacks 059M), so for a
countably generated module the three hypotheses together are *equivalent* to the conclusion. What
fails without countable generation is the implication proved here, not its converse (Stacks 059Y).

## Main results

* `Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated`: a flat, Mittag-Leffler,
  countably generated module is projective.

## Implementation notes

The Mittag-Leffler hypothesis is `IsMittagLeffler` of
`StacksFrontier/Algebra/MittagLeffler/Defs.lean`, the predicate of Definition 059F: every
map `f : P → M` from a finitely presented module dominates and is dominated by some map
`g : P → Q` into a finitely presented module, domination meaning `Ker(f ⊗ id_T) ⊆ Ker(g ⊗ id_T)`
for every `R`-module `T`. It is cited by its name there rather than restated, so that this lemma
and Definition 059F speak of the same notion; its form with the condition written out inline is
identified with it by `isMittagLeffler_def_iff`. Likewise countable generation is
`Module.CountablyGenerated` of `StacksFrontier/RingTheory/Flat/FaithfullyFlat/Descent.lean`, the
predicate of Lemma 0GVD, rather than the unfolded
`∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤`.

`IsMittagLeffler` carries an independent universe for each of the ring, the module, the finitely
presented modules `P` and `Q`, and the test module `T`; here the last three are instantiated at the
universe `v` of `M`, whence `Small.{v} R`. For a `v`-small `R` every finitely presented `R`-module
is isomorphic to one in `Type v` and domination may be tested on finitely presented modules alone
(Stacks 059C), so the condition at these universes is the source's quantification over all modules.
Without smallness the quantifications over `Type v` are neither the source's nor comparable with
them, `P` and `T` occurring on opposite sides. The hypothesis holds automatically when `R` and `M`
share a universe.

Flatness is `Module.Flat R M` and projectivity is `Module.Projective R M`, taken as instance and
conclusion in the shape of the Mathlib sibling `Module.Flat.projective_of_finitePresentation`, of
which this is the variant with finite presentation weakened to Mittag-Leffler plus countable
generation; the name is that sibling's with the weakened hypotheses substituted, in the source's
order.

Faithfulness. (1) No hypothesis is dead. Flatness is what produces the colimit of finite free
modules, without which the `Hom(M i, -)` sequences are not exact — over `R = ℤ` the module `ℤ/2` is
countably generated and Mittag-Leffler, being finitely presented (Stacks 059R (1)), and is not
projective. Countable generation is what makes the index set countable so that Stacks 0598 applies,
and the conclusion is false without it: `ℤ[[x]]` is a flat Mittag-Leffler `ℤ`-module that is not
projective (Stacks 059Y). The Mittag-Leffler hypothesis is what makes the system of duals
Mittag-Leffler, and the conclusion is false without it too: `ℤ[1/2]` is a flat, countably generated
`ℤ`-module which is not free, hence not projective, subgroups of free abelian groups being free.
Smallness is used through `Shrink.{v} R`, the free module on the underlying set of `M` with its
scalars transported into `Type v` being the free cover of `M` the argument runs on. (2) The scalars
and the base are the source's: `M` is an `R`-module, the test maps and their tensor products in the
Mittag-Leffler condition are `R`-linear over `R`, the spanning set spans over `R`, and flatness and
projectivity are over `R`; nothing is localized or base changed. (3) The statement names no
canonical map, and neither does the source; the conclusion is Mathlib's `Module.Projective R M`,
the lifting property against surjections, rather than the weaker assertion that some surjection
from a free module onto `M` exists. (4) The instantiation is not degenerate: for `R = ℤ` and
`M = ⨁ (_ : ℕ), ℤ` all three hypotheses hold — `M` is free, hence flat and Mittag-Leffler (Stacks
059R (2)), and it is countably generated by the coordinate vectors — while `M` is not finitely
generated, so the conclusion is not an instance of
`Module.Flat.projective_of_finitePresentation`.

## References

* [Stacks project, Tag 059X](https://stacks.math.columbia.edu/tag/059X)
-/

/-- **Stacks 059X.** A flat, Mittag-Leffler, countably generated module over a commutative ring is
projective. The Mittag-Leffler condition is `IsMittagLeffler` (Definition 059F), with its finitely
presented modules and test modules taken in the universe of `M`; countable generation is
`Module.CountablyGenerated`, the existence of a countable spanning set. -/
@[stacks 059X "Mittag-Leffler is `IsMittagLeffler` (059F) and countable generation is
`Module.CountablyGenerated` (from Tag 0GVD), both cited by name; the companion statements write them
out inline, `isMittagLeffler_def_iff` identifying the two forms. Test data in the universe of `M`,
whence `Small.{v} R`. See the module docstring."]
public theorem Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hML : IsMittagLeffler.{u, v, v, v, v} R M)
    (hcg : Module.CountablyGenerated R M) :
    Module.Projective R M :=
  Stacks.MittagLeffler.FlatIsProjective.solution R M hcg fun P _ _ _ f ↦
    (isMittagLeffler_def_iff R M).1 hML P f

end
