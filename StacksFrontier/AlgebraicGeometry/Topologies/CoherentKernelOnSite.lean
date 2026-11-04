module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kernels of coherent sheaves of modules on a site

Let `R` be a sheaf of rings on an arbitrary site and let `N` be a sheaf of `R`-modules which is
coherent in the sense of Stacks 03DL(8), that is, `SheafOfModules.IsCoherentOnSite N`.  The
kernel of any morphism into `N` from a sheaf of modules of finite type is again of finite type,
and the kernel of a morphism of coherent sheaves of modules is coherent.  These are parts (2)
and (3) of Stacks 01BY, proved here for the site-level coherence predicate rather than for the
ringed-space predicate `Stacks.SheafOfModules.IsCoherent` of Stacks 01BV.

## Main results

* `Stacks.SheafOfModules.isFiniteType_kerObj_of_isCoherentOnSite` and
  `Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherentOnSite`: **Stacks 01BY (2) on a
  site.**  The kernel of a morphism from a sheaf of modules of finite type to a coherent sheaf
  of modules is of finite type, in the sectionwise sense `PresheafOfModules.IsFiniteType` which
  is the finite-type clause of `SheafOfModules.IsCoherentOnSite`.
* `Stacks.SheafOfModules.isCoherentOnSite_of_injective`: **Stacks 01BY (1) on a site.**  A
  sheaf of modules of finite type which is a subobject of a coherent sheaf of modules is
  coherent.
* `Stacks.SheafOfModules.isCoherentOnSite_kerObj` and
  `Stacks.SheafOfModules.isCoherentOnSite_kernel`: **Stacks 01BY (3), kernels, on a site.**
* `Stacks.SheafOfModules.isCoherentOnSite_of_iso`: coherence on a site is invariant under
  isomorphism.
* `Stacks.SheafOfModules.generates_kerSectionOfRelation` is the local step on which part (2)
  rests: over an object of the site carrying a finite generating family `s` of the source, the
  relations among the images of `s` give, after a further covering, a finite generating family
  of the kernel.
* `Stacks.SheafOfModules.presheaf_isFiniteType_of_coversTop` and
  `Stacks.SheafOfModules.presheaf_isFiniteType_of_iso`: the sectionwise finite-type condition
  may be tested on a covering family indexed in any universe, and transports along an
  isomorphism of presheaves of modules.

## Implementation notes

**Why this is not a corollary of the ringed-space theory.**  The closure properties of Stacks
01BY that the library already has
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentWeakSerre.lean`) are about
`Stacks.SheafOfModules.IsCoherent`, whose kernel clause asks that the kernel of every morphism
`free I ⟶ M|_U` out of a finite free sheaf of modules be of finite type in Mathlib's sense.  The
predicate the algebraic-spaces side uses, `SheafOfModules.IsCoherentOnSite`, asks instead that
the *sectionwise* sheaf of relations `PresheafOfModules.relations` among every finite family of
sections be of finite type in the *sectionwise* sense `PresheafOfModules.IsFiniteType`.  No
comparison between the two shapes exists in the library, so neither clause can be obtained from
the other, and the ringed-space development is in addition equi-universe (`C : Type u` with
`Category.{u} C` and `RingCat.{u}`) while the small étale site of an algebraic space has its
objects in `Type (u + 1)` and its morphisms in `Type u`.  Everything here is therefore proved
directly in the sectionwise language, at four independent universes: the objects of the site,
its morphisms, the coefficient ring and the module sections.

**No sheafification hypotheses are needed anywhere.**  The sectionwise conditions are
statements about restriction maps and linear combinations, not about free sheaves of modules,
and the kernel used is the sectionwise one, `SheafOfModules.kerObj`, which exists over any site
by `SheafOfModules.kerIsLimit`.  The honest categorical kernel is identified with it by
`Stacks.SheafOfModules.kernelIsoKerObj`, using only that the category of sheaves of modules has
finite limits.

**The shape of the proof of part (2).**  Let `φ : M ⟶ N` with `M` of finite type and `N`
coherent.  Over an object `A` carrying a finite family `s` of generators of `M`, the images
`φ(s)` are a finite family of sections of `N`, so the relations among them form a presheaf of
modules on the slice site at `A` which is of finite type by coherence of `N`.  A relation
`ρ` over an object `Z` of that slice site is a tuple of coefficients killing `φ(s)`, so the
corresponding combination `∑ ρᵢ · sᵢ` is a section of the kernel over `Z.left`
(`kerSectionOfRelation`); and those sections generate the kernel, because a section of the
kernel is locally a combination of the `s`, its coefficient tuple is then a relation, and that
relation is in turn locally a combination of the chosen generating relations.  That is two
successive coverings, which `generates_of_bind` composes into one by `Sieve.bind`.  The objects
`Z.left`, as `A` and `Z` range over the two covering families, cover the final object by
`CategoryTheory.GrothendieckTopology.CoversTop.over`; their index type lives in `Type (max u v)`
rather than in `Type u`, which is why `presheaf_isFiniteType_of_coversTop` shrinks it.

**Part (1) is cheap in this language.**  The relations among a finite family of sections of a
subobject are *equal*, as a submodule of a finite product of copies of the ring, to the
relations among their images, because the inclusion is injective on sections; so
`relationsIsoOfInjective` is an isomorphism whose components are `LinearEquiv.ofEq`.

**What is not proved here.**  Parts (3) for cokernels and (4) for extensions need the
sectionwise form of Stacks 01B7 — that the middle term of a short exact sequence with outer
terms of finite type is of finite type — which in turn needs sections of the quotient to lift
locally, that is, a characterization of epimorphisms of sheaves of modules.  That is where the
sheafification hypotheses enter, and none of it is done here.

**Namespace.**  The declarations live in `Stacks.SheafOfModules`, next to the ringed-space
theory, rather than in `SheafOfModules`, so that this file can be co-imported with the rest of
the library.  The sectionwise kernel is Mathlib's `SheafOfModules.Submodule` machinery as
packaged by `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`; nothing of
it is redefined.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules SheafOfModules

universe u v w m

namespace Stacks.SheafOfModules

/-! ### Elementary identities about sections and linear combinations -/

section Elementary

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- A morphism of presheaves of modules is linear on sections. -/
lemma hom_app_smul {P Q : PresheafOfModules.{m} R} (φ : P ⟶ Q) (X : Cᵒᵖ) (a : R.obj X)
    (z : P.obj X) : Hom.app φ X (a • z) = a • Hom.app φ X z :=
  (ConcreteCategory.hom (Hom.app φ X)).map_smul a z

/-- The restriction of a linear combination of sections is the linear combination of the
restrictions, with the coefficients restricted along the structure map of the ring. -/
lemma map_sum_smul {P : PresheafOfModules.{m} R} {X Y : Cᵒᵖ} (h : X ⟶ Y) {n : ℕ}
    (b : Fin n → R.obj X) (z : Fin n → P.obj X) :
    P.map h (∑ i, b i • z i) = ∑ i, R.map h (b i) • P.map h (z i) :=
  (map_sum (ConcreteCategory.hom (P.map h)) (fun i => b i • z i) Finset.univ).trans
    (Finset.sum_congr rfl (fun i _ => P.map_smul h (b i) (z i)))

/-- The restriction maps of the presheaf of relations among a finite family of sections act
coefficientwise. -/
lemma relations_map_apply_val {P : PresheafOfModules.{m} R} {U : C} {n : ℕ}
    (s : Fin n → P.obj (op U)) {V W : Over U} (h : W ⟶ V)
    (y : (relations P s).obj (op V)) (i : Fin n) :
    ((relations P s).map h.op y).val i = R.map h.left.op (y.val i) := rfl

/-- A morphism of presheaves of modules maps a linear combination of restrictions to the linear
combination of the restrictions of the images. -/
private theorem hom_app_sum_smul_map {P Q : PresheafOfModules.{m} R} (φ : P ⟶ Q) {X Y : Cᵒᵖ}
    (h : X ⟶ Y) {n : ℕ} (a : Fin n → R.obj Y) (z : Fin n → P.obj X) :
    Hom.app φ Y (∑ i, a i • P.map h (z i)) = ∑ i, a i • Q.map h (Hom.app φ X (z i)) := by
  refine (map_sum (ConcreteCategory.hom (Hom.app φ Y)) (fun i => a i • P.map h (z i))
    Finset.univ).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (hom_app_smul φ Y (a i) _).trans (congrArg (a i • ·) (naturality_apply φ h (z i)))

end Elementary

section Algebra

/-- The underlying element of a linear combination formed inside a submodule. -/
lemma coe_sum_smul {A : Type*} [Ring A] {Mod : Type*} [AddCommGroup Mod] [Module A Mod]
    {q : Submodule A Mod} {p : ℕ} (d : Fin p → A) (y : Fin p → q) :
    ((∑ j, d j • y j : q) : Mod) = ∑ j, d j • (y j : Mod) := by
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]

/-- Coefficientwise form of `Stacks.SheafOfModules.coe_sum_smul` for a submodule of a finite
product of copies of the ring. -/
lemma coe_sum_smul_apply {A : Type*} [Ring A] {n p : ℕ} {q : Submodule A (Fin n → A)}
    (d : Fin p → A) (y : Fin p → q) (i : Fin n) :
    ((∑ j, d j • y j : q) : Fin n → A) i = ∑ j, d j * (y j : Fin n → A) i := by
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Collecting a linear combination of linear combinations. -/
lemma sum_smul_sum_smul_of_fin {A : Type*} [Ring A] {Mod : Type*} [AddCommGroup Mod]
    [Module A Mod] {p n : ℕ} (c : Fin p → A) (b : Fin p → Fin n → A) (z : Fin n → Mod) :
    ∑ j, c j • (∑ i, b j i • z i) = ∑ i, (∑ j, c j * b j i) • z i := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end Algebra

/-! ### The sectionwise finite-type condition -/

section SectionwiseFiniteType

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {J : GrothendieckTopology C}

/-- Generation by finitely many sections transports along an isomorphism of presheaves of
modules. -/
theorem generates_of_iso {P Q : PresheafOfModules.{m} R} (e : P ≅ Q) {U : C} {n : ℕ}
    {x : Fin n → P.obj (op U)} (hx : Generates J P x) :
    Generates J Q (fun i => Hom.app e.hom (op U) (x i)) := by
  intro V f t
  obtain ⟨S, hS, hgen⟩ := hx V f (Hom.app e.inv (op V) t)
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨a, ha⟩ := hgen W g hg
  refine ⟨a, ?_⟩
  simp only [restrictₛₗ_apply] at ha ⊢
  refine (hom_app_sum_smul_map e.hom _ a x).symm.trans ?_
  refine (congrArg (fun z => Hom.app e.hom (op W) z) ha).trans ?_
  rw [naturality_apply]
  exact congrArg (fun z => Q.map g.op z)
    (congrArg (fun z : Q ⟶ Q => Hom.app z (op V) t) e.inv_hom_id)

/-- Generation by finitely many sections may be checked after passing to a further covering: if
every section is, locally, locally a linear combination of the given family, then the family
generates.  The two coverings are composed by `CategoryTheory.Sieve.bind`. -/
theorem generates_of_bind {P : PresheafOfModules.{m} R} {Y : C} {n : ℕ}
    (x : Fin n → P.obj (op Y))
    (h : ∀ (V : C) (f : V ⟶ Y) (t : P.obj (op V)), ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (g : W ⟶ V), S g → ∃ T : Sieve W, T ∈ J W ∧
        ∀ (Z : C) (k : Z ⟶ W), T k → ∃ a : Fin n → R.obj (op Z),
          ∑ i, a i • P.restrictₛₗ ((k ≫ g) ≫ f).op (x i) = P.restrictₛₗ (k ≫ g).op t) :
    Generates J P x := by
  intro V f t
  obtain ⟨S, hS, hST⟩ := h V f t
  choose T hT hTa using hST
  refine ⟨_, J.bind_covering hS (fun W g hg => hT W g hg), ?_⟩
  rintro Z k ⟨W, k', g, hg, hk', rfl⟩
  exact hTa W g hg Z k' hk'

/-- The sectionwise finite-type condition may be tested on any family covering the final object,
indexed in any universe: the index type is shrunk to the subtype of those objects of the site
which carry finitely many generating sections. -/
theorem presheaf_isFiniteType_of_coversTop {P : PresheafOfModules.{m} R} {ι : Type*}
    (U : ι → C) (hU : J.CoversTop U)
    (h : ∀ i, ∃ (n : ℕ) (x : Fin n → P.obj (op (U i))), Generates J P x) :
    PresheafOfModules.IsFiniteType J P := by
  refine ⟨{ Y : C // ∃ (n : ℕ) (x : Fin n → P.obj (op Y)), Generates J P x },
    Subtype.val, fun Y => ?_, fun Y => Y.2⟩
  refine J.superset_covering (fun Z f hf => ?_) (hU Y)
  obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff _ f).1 hf
  exact (Sieve.mem_ofObjects_iff _ f).2 ⟨⟨U i, h i⟩, ⟨hi⟩⟩

/-- The sectionwise finite-type condition transports along an isomorphism of presheaves of
modules. -/
theorem presheaf_isFiniteType_of_iso {P Q : PresheafOfModules.{m} R} (e : P ≅ Q)
    (h : PresheafOfModules.IsFiniteType J P) : PresheafOfModules.IsFiniteType J Q := by
  obtain ⟨I, U, hU, hgen⟩ := h.exists_generators
  refine ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨n, s, hs⟩ := hgen i
  exact ⟨n, _, generates_of_iso e hs⟩

end SectionwiseFiniteType

/-! ### Sections of the kernel coming from relations -/

section Kernel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The categorical kernel of a morphism of sheaves of modules is its sectionwise kernel. -/
noncomputable def kernelIsoKerObj {M N : SheafOfModules.{m} R} (φ : M ⟶ N) :
    kernel φ ≅ _root_.SheafOfModules.kerObj φ :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) (_root_.SheafOfModules.kerIsLimit φ)

variable {M N : SheafOfModules.{m} R} (φ : M ⟶ N) {A : C} {n : ℕ}
  (s : Fin n → M.val.obj (op A))

/-- The images under `φ` of a finite family of sections of `M` over `A`. -/
noncomputable abbrev imageSections : Fin n → N.val.obj (op A) :=
  fun i => Hom.app φ.val (op A) (s i)

/-- A relation among the images of `s` over an object `Z` of the slice site at `A` gives a
section of the kernel of `φ` over `Z.left`: the corresponding linear combination of the
restrictions of `s`, which `φ` kills precisely because the coefficients are a relation. -/
noncomputable def kerSectionOfRelation (Z : Over A)
    (ρ : (relations N.val (imageSections φ s)).obj (op Z)) :
    (_root_.SheafOfModules.kerObj φ).val.obj (op Z.left) :=
  ⟨∑ i, ρ.val i • M.val.map Z.hom.op (s i), by
    change Hom.app φ.val (op Z.left) (∑ i, ρ.val i • M.val.map Z.hom.op (s i)) = 0
    refine Eq.trans (map_sum (ConcreteCategory.hom (Hom.app φ.val (op Z.left)))
      (fun i => ρ.val i • M.val.map Z.hom.op (s i)) Finset.univ) ?_
    refine Eq.trans (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      show Hom.app φ.val (op Z.left) (ρ.val i • M.val.map Z.hom.op (s i))
          = ρ.val i • N.val.map Z.hom.op (Hom.app φ.val (op A) (s i)) from
        (hom_app_smul φ.val (op Z.left) (ρ.val i) _).trans
          (congrArg (fun z => ρ.val i • z) (naturality_apply φ.val Z.hom.op (s i))))) ?_
    have hp := ρ.property
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hp
    exact hp⟩

/-- **The local step of Stacks 01BY (2) on a site.**  If `s` is a finite family of sections
generating `M` over `A`, and `r` is a finite family of relations among the images of `s`
generating the relations over an object `Z` of the slice site at `A`, then the associated
combinations `kerSectionOfRelation φ s Z (r j)` generate the kernel of `φ` over `Z.left`.

A section `τ` of the kernel over an object `V` above `Z.left` is, on a covering of `V`, a
combination `∑ aᵢ · sᵢ`; applying `φ` shows that the coefficient tuple `a` is a relation among
the images of `s`, so on a further covering it is a combination `∑ cⱼ · rⱼ`, and then
`∑ cⱼ · kerSectionOfRelation φ s Z (r j)` restricts to `τ`. -/
theorem generates_kerSectionOfRelation (hs : Generates J M.val s)
    {Z : Over A} {p : ℕ}
    (r : Fin p → (relations N.val (imageSections φ s)).obj (op Z))
    (hr : Generates (J.over A) (relations N.val (imageSections φ s)) r) :
    Generates J (_root_.SheafOfModules.kerObj φ).val
      (fun j => kerSectionOfRelation φ s Z (r j)) := by
  refine generates_of_bind _ (fun V f τ => ?_)
  obtain ⟨S, hS, hA⟩ := hs V (f ≫ Z.hom) τ.val
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨a, ha⟩ := hA W g hg
  have hrel : a ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op W))
      (fun i => N.val.restrictₛₗ (g ≫ f ≫ Z.hom).op (imageSections φ s i))) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    have hL : Hom.app φ.val (op W) (∑ i, a i • M.val.map (g ≫ f ≫ Z.hom).op (s i))
        = ∑ i, a i • N.val.map (g ≫ f ≫ Z.hom).op (imageSections φ s i) :=
      hom_app_sum_smul_map φ.val (g ≫ f ≫ Z.hom).op a s
    have hR : Hom.app φ.val (op W) (M.val.map g.op τ.val) = 0 :=
      (naturality_apply φ.val g.op τ.val).trans
        (by rw [show Hom.app φ.val (op V) τ.val = 0 from τ.2]; exact map_zero _)
    exact hL.symm.trans ((congrArg (fun z => Hom.app φ.val (op W) z) ha).trans hR)
  let W' : Over A := Over.mk (g ≫ f ≫ Z.hom)
  let ρ : (relations N.val (imageSections φ s)).obj (op W') := ⟨a, hrel⟩
  let θ : W' ⟶ Z := Over.homMk (g ≫ f) (Category.assoc g f Z.hom)
  obtain ⟨S₂, hS₂, hB⟩ := hr W' θ ρ
  refine ⟨Sieve.overEquiv W' S₂, (J.mem_over_iff S₂).1 hS₂, fun Z' k hk => ?_⟩
  let κ : Over.mk (k ≫ W'.hom) ⟶ W' := Over.homMk k rfl
  obtain ⟨c, hc⟩ := hB (Over.mk (k ≫ W'.hom)) κ ((Sieve.overEquiv_iff S₂ k).1 hk)
  refine ⟨c, ?_⟩
  let c' : Fin p → R.obj.obj (op Z') := fun j => c j
  have key : ∀ i, (∑ j, c' j * R.obj.map (k ≫ g ≫ f).op ((r j).val i))
      = R.obj.map k.op (a i) := fun i =>
    (Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      congrArg (fun z => c' j * z)
        (relations_map_apply_val (imageSections φ s) (κ ≫ θ) (r j) i).symm)).trans
      ((coe_sum_smul_apply c' _ i).symm.trans ((congrFun (Subtype.ext_iff.1 hc) i).trans
        (relations_map_apply_val (imageSections φ s) κ ρ i)))
  have key' : ∀ i, (∑ j, c' j * R.obj.map ((k ≫ g) ≫ f).op ((r j).val i))
      = R.obj.map k.op (a i) := by
    intro i
    rw [Category.assoc]
    exact key i
  have e1 : ∀ (Y : C) (h : Y ⟶ Z.left) (h' : Y ⟶ A) (_ : h ≫ Z.hom = h')
      (ρ' : (relations N.val (imageSections φ s)).obj (op Z)),
      Subtype.val ((_root_.SheafOfModules.kerObj φ).val.restrictₛₗ h.op
          (kerSectionOfRelation φ s Z ρ'))
        = ∑ i, R.obj.map h.op (ρ'.val i) • M.val.map h'.op (s i) := by
    intro Y h h' hh ρ'
    subst hh
    show M.val.map h.op (∑ i, ρ'.val i • M.val.map Z.hom.op (s i)) = _
    refine (map_sum_smul h.op (fun i => ρ'.val i)
      (fun i => M.val.map Z.hom.op (s i))).trans ?_
    exact Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      congrArg (fun z => R.obj.map h.op (ρ'.val i) • z)
        ((map_comp_apply M.val Z.hom.op h.op (s i)).symm.trans
          (M.val.congr_map_apply (by simp only [← op_comp]) (s i))))
  refine Subtype.ext ?_
  have st1 : Subtype.val (∑ j, c j • (_root_.SheafOfModules.kerObj φ).val.restrictₛₗ
          ((k ≫ g) ≫ f).op (kerSectionOfRelation φ s Z (r j)))
      = ∑ j, c' j • Subtype.val ((_root_.SheafOfModules.kerObj φ).val.restrictₛₗ
          ((k ≫ g) ≫ f).op (kerSectionOfRelation φ s Z (r j))) :=
    coe_sum_smul c' (fun j => (_root_.SheafOfModules.kerObj φ).val.restrictₛₗ ((k ≫ g) ≫ f).op
      (kerSectionOfRelation φ s Z (r j)))
  have st2 : ∑ j, c' j • Subtype.val ((_root_.SheafOfModules.kerObj φ).val.restrictₛₗ
          ((k ≫ g) ≫ f).op (kerSectionOfRelation φ s Z (r j)))
      = ∑ j, c' j • (∑ i, R.obj.map ((k ≫ g) ≫ f).op ((r j).val i) •
          M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i)) :=
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      congrArg (fun z => c' j • z) (e1 Z' ((k ≫ g) ≫ f) (k ≫ g ≫ f ≫ Z.hom)
        (by simp only [Category.assoc]) (r j)))
  have st3 : ∑ j, c' j • (∑ i, R.obj.map ((k ≫ g) ≫ f).op ((r j).val i) •
          M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i))
      = ∑ i, (∑ j, c' j * R.obj.map ((k ≫ g) ≫ f).op ((r j).val i)) •
          M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i) :=
    sum_smul_sum_smul_of_fin c' (fun j i => R.obj.map ((k ≫ g) ≫ f).op ((r j).val i))
      (fun i => M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i))
  have st4 : ∑ i, (∑ j, c' j * R.obj.map ((k ≫ g) ≫ f).op ((r j).val i)) •
          M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i)
      = ∑ i, R.obj.map k.op (a i) • M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i) :=
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      congrArg (fun z => z • M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i)) (key' i))
  have st5 : M.val.map k.op (∑ i, a i • M.val.map (g ≫ f ≫ Z.hom).op (s i))
      = ∑ i, R.obj.map k.op (a i) • M.val.map (k ≫ g ≫ f ≫ Z.hom).op (s i) :=
    (map_sum_smul k.op a (fun i => M.val.map (g ≫ f ≫ Z.hom).op (s i))).trans
      (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        congrArg (fun z => R.obj.map k.op (a i) • z)
          ((map_comp_apply M.val (g ≫ f ≫ Z.hom).op k.op (s i)).symm.trans
            (M.val.congr_map_apply (by simp only [← op_comp]) (s i)))))
  have st6 : M.val.map k.op (∑ i, a i • M.val.map (g ≫ f ≫ Z.hom).op (s i))
      = Subtype.val ((_root_.SheafOfModules.kerObj φ).val.restrictₛₗ (k ≫ g).op τ) :=
    (congrArg (fun z => M.val.map k.op z) ha).trans
      ((map_comp_apply M.val g.op k.op τ.val).symm.trans
        (M.val.congr_map_apply (by simp only [← op_comp]) τ.val))
  exact st1.trans (st2.trans (st3.trans (st4.trans (st5.symm.trans st6))))

end Kernel

/-! ### Subobjects of a coherent sheaf of modules -/

section Subobject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A monomorphism of sheaves of modules is injective on sections. -/
lemma injective_val_of_mono {K M : SheafOfModules.{m} R} (ι : K ⟶ M) [Mono ι] (X : Cᵒᵖ) :
    Function.Injective (Hom.app ι.val X) :=
  PresheafOfModules.injective_of_mono ((_root_.SheafOfModules.forget R).map ι) X

/-- The relations among a finite family of sections of a subobject are the relations among their
images: the two are the same submodule of a finite product of copies of the ring, because the
inclusion is injective on sections. -/
noncomputable def relationsIsoOfInjective {K M : SheafOfModules.{m} R} (ι : K ⟶ M)
    (hι : ∀ X, Function.Injective (Hom.app ι.val X))
    {U : C} {n : ℕ} (x : Fin n → K.val.obj (op U)) :
    relations K.val x ≅ relations M.val (fun i => Hom.app ι.val (op U) (x i)) := by
  refine PresheafOfModules.isoMk (fun V => (LinearEquiv.ofEq _ _ ?_).toModuleIso) ?_
  · refine Submodule.ext (fun c => ?_)
    rw [LinearMap.mem_ker, LinearMap.mem_ker, Fintype.linearCombination_apply,
      Fintype.linearCombination_apply]
    have hmap : ∑ i, c i • M.val.restrictₛₗ V.unop.hom.op (Hom.app ι.val (op U) (x i))
        = Hom.app ι.val (op V.unop.left) (∑ i, c i • K.val.restrictₛₗ V.unop.hom.op (x i)) :=
      ((map_sum (ConcreteCategory.hom (Hom.app ι.val (op V.unop.left)))
        (fun i => c i • K.val.map V.unop.hom.op (x i)) Finset.univ).trans
        (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
          (hom_app_smul ι.val (op V.unop.left) (c i) _).trans
            (congrArg (fun z => c i • z)
              (naturality_apply ι.val V.unop.hom.op (x i)))))).symm
    rw [hmap]
    exact ⟨fun h => by rw [h]; exact map_zero _,
      fun h => hι _ (h.trans (map_zero _).symm)⟩
  · intro V V' h
    ext c
    exact Subtype.ext rfl

/-- **Stacks 01BY (1) on a site.**  A sheaf of modules of finite type which is a subobject of a
coherent sheaf of modules is coherent: the relations among a finite family of its sections are
the relations among their images, which are of finite type by coherence of the ambient sheaf. -/
theorem isCoherentOnSite_of_injective {K M : SheafOfModules.{m} R} (ι : K ⟶ M)
    (hι : ∀ X, Function.Injective (Hom.app ι.val X))
    (hK : PresheafOfModules.IsFiniteType J K.val) (hM : IsCoherentOnSite M) :
    IsCoherentOnSite K where
  isFiniteType := hK
  kernel_isFiniteType U n x :=
    presheaf_isFiniteType_of_iso (relationsIsoOfInjective ι hι x).symm
      (hM.kernel_isFiniteType U n (fun i => Hom.app ι.val (op U) (x i)))

/-- Coherence on a site is invariant under isomorphism. -/
theorem isCoherentOnSite_of_iso {M N : SheafOfModules.{m} R} (e : M ≅ N)
    (hM : IsCoherentOnSite M) : IsCoherentOnSite N :=
  isCoherentOnSite_of_injective e.inv (injective_val_of_mono e.inv)
    (presheaf_isFiniteType_of_iso ((_root_.SheafOfModules.forget R).mapIso e) hM.isFiniteType) hM

end Subobject

/-! ### Stacks 01BY, parts (2) and (3) for kernels, on a site -/

section Main

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Stacks 01BY (2) on a site.**  The kernel of a morphism from a sheaf of modules of finite
type to a coherent sheaf of modules is of finite type.  Both conditions are the sectionwise ones
used by `SheafOfModules.IsCoherentOnSite`, and the kernel is the sectionwise kernel. -/
theorem isFiniteType_kerObj_of_isCoherentOnSite {M N : SheafOfModules.{m} R}
    (hM : PresheafOfModules.IsFiniteType J M.val) (hN : IsCoherentOnSite N) (φ : M ⟶ N) :
    PresheafOfModules.IsFiniteType J (_root_.SheafOfModules.kerObj φ).val := by
  obtain ⟨I, A, hA, hgen⟩ := hM.exists_generators
  choose n s hs using hgen
  choose I' Zc hZc hgen' using fun i =>
    (hN.kernel_isFiniteType (A i) (n i) (imageSections φ (s i))).exists_generators
  choose q r hr using hgen'
  exact presheaf_isFiniteType_of_coversTop
    (ι := (i : I) × I' i) (fun ij => (Zc ij.1 ij.2).left) (hA.over hZc) (fun ij =>
      ⟨q ij.1 ij.2, _, generates_kerSectionOfRelation φ (s ij.1) (hs ij.1)
        (r ij.1 ij.2) (hr ij.1 ij.2)⟩)

/-- **Stacks 01BY (2) on a site**, for the kernel formed in the category of sheaves of
modules. -/
theorem isFiniteType_kernel_of_isCoherentOnSite {M N : SheafOfModules.{m} R}
    (hM : PresheafOfModules.IsFiniteType J M.val) (hN : IsCoherentOnSite N) (φ : M ⟶ N) :
    PresheafOfModules.IsFiniteType J (kernel φ).val :=
  presheaf_isFiniteType_of_iso
    ((_root_.SheafOfModules.forget R).mapIso (kernelIsoKerObj φ)).symm
    (isFiniteType_kerObj_of_isCoherentOnSite hM hN φ)

/-- **Stacks 01BY (3), kernels, on a site.**  The sectionwise kernel of a morphism of coherent
sheaves of modules is coherent: it is of finite type by part (2) and it is a subobject of the
coherent source, so part (1) applies. -/
@[ega "0 5.3.4" "more general"]
theorem isCoherentOnSite_kerObj {M N : SheafOfModules.{m} R} (hM : IsCoherentOnSite M)
    (hN : IsCoherentOnSite N) (φ : M ⟶ N) :
    IsCoherentOnSite (_root_.SheafOfModules.kerObj φ) :=
  isCoherentOnSite_of_injective (_root_.SheafOfModules.kerIota φ)
    (injective_val_of_mono (_root_.SheafOfModules.kerIota φ))
    (isFiniteType_kerObj_of_isCoherentOnSite hM.isFiniteType hN φ) hM

/-- **Stacks 01BY (3), kernels, on a site**, for the kernel formed in the category of sheaves of
modules. -/
theorem isCoherentOnSite_kernel {M N : SheafOfModules.{m} R} (hM : IsCoherentOnSite M)
    (hN : IsCoherentOnSite N) (φ : M ⟶ N) : IsCoherentOnSite (kernel φ) :=
  isCoherentOnSite_of_iso (kernelIsoKerObj φ).symm (isCoherentOnSite_kerObj hM hN φ)

end Main

end Stacks.SheafOfModules

end
