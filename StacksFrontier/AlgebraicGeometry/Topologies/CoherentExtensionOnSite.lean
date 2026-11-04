module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extensions of coherent sheaves of modules on a site

Let `R` be a sheaf of rings on an arbitrary site and grade the sheaves of modules over it by the
sectionwise coherence predicate `Stacks.SheafOfModules.IsCoherentOnSite` of Stacks 03DL(8).  An
extension of coherent sheaves of modules is coherent, which is part (4) of Stacks 01BY, and the
middle term of a short exact sequence whose outer terms are of finite type in the sectionwise
sense is of finite type, which is the second assertion of Stacks 01B7.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_middle` and
  `Stacks.SheafOfModules.isCoherentOnSite_X₂_of_shortExact`: an extension of coherent sheaves of
  modules on a site is coherent (Stacks 01BY (4)).
* `Stacks.SheafOfModules.presheaf_isFiniteType_relations_X₂`: if `ι` is a kernel of `p` and the
  outer terms are coherent, the relations among any finite family of sections of the middle term
  are of finite type.
* `Stacks.SheafOfModules.generates_relations_middle`: a finite generating family of the
  relations among finitely many sections of the middle term, built from generating families of
  relations in the outer terms.
* `Stacks.SheafOfModules.presheaf_isFiniteType_X₂`: the middle term of a kernel–cokernel pair
  with locally surjective projection is of finite type when the outer terms are, in the
  sectionwise sense (Stacks 01B7, second assertion).
* `Stacks.SheafOfModules.generates_middle_of_lifts`: the images of generators of the first term
  together with lifts of generators of the third term generate the middle term.
* `Stacks.SheafOfModules.isLocallySurjective_of_isColimit`: a cokernel projection of sheaves of
  modules is locally surjective on sections.

## Implementation notes

The statements proved from an explicit kernel fork and cokernel cofork need no hypothesis on the
category of sheaves of modules. The `ShortComplex` form assumes the ambient category balanced,
which makes the first term of a short exact sequence a kernel of the second map and the third
term a cokernel of the first (`CategoryTheory.ShortComplex.ShortExact.fIsKernel` and
`CategoryTheory.ShortComplex.ShortExact.gIsCokernel`). No sheafification hypothesis occurs.

The relations clause, `presheaf_isFiniteType_relations_X₂`, uses only that `ι` is a kernel of
`p`, not local surjectivity of `p`.

The sectionwise restriction lemmas live in the namespaces `Stacks.SheafOfModules.Sectionwise`
and `Stacks.SheafOfModules.LocalImage`, and the prefix `presheaf_` marks statements about the
sectionwise predicate `PresheafOfModules.IsFiniteType`.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules SheafOfModules

universe u v w m

namespace Stacks.SheafOfModules

/-! ### Generating families and local surjectivity -/

section Sectionwise

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {J : GrothendieckTopology C}

/-- Iterated restriction of a section is restriction along the composite. -/
lemma restrict_restrict {P : PresheafOfModules.{m} R} {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : P.obj (op U)) :
    P.restrictₛₗ g.op (P.restrictₛₗ f.op x) = P.restrictₛₗ (g ≫ f).op x :=
  (P.map_comp_apply f.op g.op x).symm.trans (P.congr_map_apply (by simp only [← op_comp]) x)

namespace Sectionwise

/-- The restriction of a generating family is a generating family for the restricted
section. -/
theorem generates_restrict {P : PresheafOfModules.{m} R} {U V : C} (h : V ⟶ U) {n : ℕ}
    (s : Fin n → P.obj (op U)) (hs : Generates J P s) :
    Generates J P (fun i ↦ P.restrictₛₗ h.op (s i)) := by
  intro W g t
  obtain ⟨S, hS, hgen⟩ := hs W (g ≫ h) t
  refine ⟨S, hS, fun Z q hq ↦ ?_⟩
  obtain ⟨a, ha⟩ := hgen Z q hq
  refine ⟨a, Eq.trans (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ ?_)) ha⟩
  refine congrArg (fun z ↦ a i • z) ?_
  refine (restrict_restrict h (q ≫ g) (s i)).trans ?_
  exact P.congr_map_apply (by simp only [Category.assoc]) (s i)

/-- Iterated restriction of a section, for any factorization of the composite. -/
lemma restrict_restrict_eq {P : PresheafOfModules.{m} R} {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (h : W ⟶ U) (hh : g ≫ f = h) (x : P.obj (op U)) :
    P.restrictₛₗ g.op (P.restrictₛₗ f.op x) = P.restrictₛₗ h.op x := by
  subst hh
  exact restrict_restrict f g x

/-- Restriction of a linear combination of sections is the combination of the restrictions,
with the coefficients restricted along the structure map of the ring. -/
lemma restrict_sum_smul {P : PresheafOfModules.{m} R} {U V : C} (h : V ⟶ U) {n : ℕ}
    (a : Fin n → R.obj (op U)) (x : Fin n → P.obj (op U)) :
    P.restrictₛₗ h.op (∑ i, a i • x i) = ∑ i, R.map h.op (a i) • P.restrictₛₗ h.op (x i) := by
  simp only [map_sum, map_smulₛₗ]

end Sectionwise

open Sectionwise

/-- The objects of the site carrying a finite generating family of a presheaf of modules of
finite type cover the site: a covering family is given, and any object admitting a map to a
member of it admits the restricted family. -/
theorem coversTop_generates {P : PresheafOfModules.{m} R}
    (hP : PresheafOfModules.IsFiniteType J P) :
    J.CoversTop
      (fun i : { U : C // ∃ (n : ℕ) (s : Fin n → P.obj (op U)), Generates J P s } ↦ i.1) := by
  obtain ⟨I, U, hU, hgen⟩ := hP.exists_generators
  intro X
  refine J.superset_covering (fun V f hf ↦ ?_) (hU X)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff _ f).1 hf
  obtain ⟨n, s, hs⟩ := hgen i
  exact (Sieve.mem_ofObjects_iff _ f).2
    ⟨⟨V, n, fun j ↦ P.restrictₛₗ g.op (s j), generates_restrict g s hs⟩, ⟨𝟙 V⟩⟩

end Sectionwise

/-! ### The local image of a morphism of sheaves of modules -/

section LocalImage

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

namespace LocalImage

/-- The sieve of arrows along which the restriction of a section of the target of a morphism of
sheaves of modules lies in the image of that morphism. -/
noncomputable abbrev imageSieveOfHom {M N : SheafOfModules.{m} R} (φ : M ⟶ N) {X : Cᵒᵖ}
    (x : N.val.obj X) : Sieve X.unop :=
  Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val) x

/-- An arrow lies in `Stacks.SheafOfModules.imageSieveOfHom` exactly when the restricted
section is in the image on that object. -/
lemma mem_imageSieveOfHom {M N : SheafOfModules.{m} R} (φ : M ⟶ N) {X : Cᵒᵖ}
    (x : N.val.obj X) {V : C} (g : V ⟶ X.unop) :
    imageSieveOfHom φ x g ↔
      ∃ y : M.val.obj (op V), Hom.app φ.val (op V) y = N.val.map g.op x :=
  Iff.rfl

/-- The **local image** of a morphism of sheaves of modules: the subsheaf of modules of the
target whose sections over an object are those which are locally in the image.  Being locally in
the image is a local condition, so this is a subsheaf. -/
noncomputable def localImage {M N : SheafOfModules.{m} R} (φ : M ⟶ N) :
    _root_.SheafOfModules.Submodule N where
  obj X :=
    { carrier := {x | imageSieveOfHom φ x ∈ J X.unop}
      zero_mem' := by
        change imageSieveOfHom φ (0 : N.val.obj X) ∈ J X.unop
        have htop : imageSieveOfHom φ (0 : N.val.obj X) = ⊤ :=
          Sieve.id_mem_iff_eq_top.1
            ((mem_imageSieveOfHom φ (0 : N.val.obj X) (𝟙 X.unop)).2 ⟨0, by simp⟩)
        rw [htop]
        exact J.top_mem _
      add_mem' := by
        intro x y hx hy
        change imageSieveOfHom φ (x + y) ∈ J X.unop
        refine J.superset_covering (S := imageSieveOfHom φ x ⊓ imageSieveOfHom φ y)
          (fun V g hg ↦ ?_) (J.intersection_covering hx hy)
        obtain ⟨a, ha⟩ := (mem_imageSieveOfHom φ x g).1 hg.1
        obtain ⟨b, hb⟩ := (mem_imageSieveOfHom φ y g).1 hg.2
        refine (mem_imageSieveOfHom φ (x + y) g).2 ⟨a + b, ?_⟩
        refine (map_add (Hom.app φ.val (op V)).hom a b).trans ?_
        exact (congrArg₂ (· + ·) ha hb).trans (map_add (N.val.map g.op).hom x y).symm
      smul_mem' := by
        intro a x hx
        change imageSieveOfHom φ (a • x) ∈ J X.unop
        refine J.superset_covering (S := imageSieveOfHom φ x) (fun V g hg ↦ ?_) hx
        obtain ⟨b, hb⟩ := (mem_imageSieveOfHom φ x g).1 hg
        refine (mem_imageSieveOfHom φ (a • x) g).2 ⟨R.obj.map g.op a • b, ?_⟩
        refine (hom_app_smul φ.val (op V) (R.obj.map g.op a) b).trans ?_
        exact ((congrArg (fun z ↦ R.obj.map g.op a • z) hb).trans
          (N.val.map_smul g.op a x).symm) }
  map := by
    intro X Y g x hx
    have hx' : Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val) x
        ∈ J X.unop := hx
    have heq : Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
          (N.val.restrictₛₗ g x)
        = (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val) x).pullback
          g.unop :=
      (Presheaf.pullback_imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
        (U := X.unop) x g.unop).symm
    change Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
      (N.val.restrictₛₗ g x) ∈ J Y.unop
    rw [heq]
    exact J.pullback_stable g.unop hx'
  isSheaf := by
    intro X x hx
    refine J.transitive hx (Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf R.obj).map φ.val) x) (fun Y g hg ↦ ?_)
    have hg' : Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
        (N.val.map g.op x) ∈ J Y := hg
    have heq : (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val) x).pullback g
        = Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
          (N.val.map g.op x) :=
      Presheaf.pullback_imageSieve ((PresheafOfModules.toPresheaf R.obj).map φ.val)
        (U := X.unop) x g
    rw [heq]
    exact hg'

/-- A section lies in the local image exactly when it is locally in the image. -/
lemma mem_localImage {M N : SheafOfModules.{m} R} (φ : M ⟶ N) {X : Cᵒᵖ} (x : N.val.obj X) :
    x ∈ (localImage φ).obj X ↔ imageSieveOfHom φ x ∈ J X.unop := Iff.rfl

/-- On sections, the inclusion of a submodule of a sheaf of modules is the inclusion of a
submodule. -/
@[simp]
lemma submodule_ι_app {N : SheafOfModules.{m} R} (K : _root_.SheafOfModules.Submodule N)
    (X : Cᵒᵖ) (y : K.toSheafOfModules.val.obj X) : Hom.app K.ι.val X y = y.val := rfl

/-- A morphism of sheaves of modules factors through its local image. -/
noncomputable def toLocalImage {M N : SheafOfModules.{m} R} (φ : M ⟶ N) :
    M ⟶ (localImage φ).toSheafOfModules where
  val :=
    { app := fun X ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ⟨Hom.app φ.val X x, by
            refine (mem_localImage φ (Hom.app φ.val X x)).2 ?_
            rw [show imageSieveOfHom φ (Hom.app φ.val X x) = ⊤ from
              Presheaf.imageSieve_app ((PresheafOfModules.toPresheaf R.obj).map φ.val) x]
            exact J.top_mem _⟩
          map_add' := fun x y ↦ Subtype.ext (map_add (Hom.app φ.val X).hom x y)
          map_smul' := fun a x ↦ Subtype.ext (map_smul (Hom.app φ.val X).hom a x) }
      naturality := by
        intro X Y g
        ext x
        exact Subtype.ext (PresheafOfModules.naturality_apply φ.val g x) }

/-- On sections, the factorization through the local image is the morphism itself. -/
@[simp]
lemma toLocalImage_val_app {M N : SheafOfModules.{m} R} (φ : M ⟶ N) (X : Cᵒᵖ)
    (x : M.val.obj X) : (Hom.app (toLocalImage φ).val X x).val = Hom.app φ.val X x := rfl

/-- The factorization of a morphism through its local image recovers the morphism. -/
theorem toLocalImage_comp_ι {M N : SheafOfModules.{m} R} (φ : M ⟶ N) :
    toLocalImage φ ≫ (localImage φ).ι = φ := by
  ext X x
  exact toLocalImage_val_app φ X x

end LocalImage

open LocalImage

/-- A cokernel projection of sheaves of modules is locally surjective on sections. -/
theorem isLocallySurjective_of_isColimit {M N P : SheafOfModules.{m} R} {φ : M ⟶ N} {p : N ⟶ P}
    (hz : φ ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p hz)) :
    PresheafOfModules.IsLocallySurjective J p.val := by
  have hepi : Epi p := epi_of_isColimit_cofork hp
  have hzero : φ ≫ toLocalImage p = 0 := by
    refine (cancel_mono (localImage p).ι).mp ?_
    rw [Category.assoc, toLocalImage_comp_ι, hz, zero_comp]
  obtain ⟨q, hq⟩ := CokernelCofork.IsColimit.desc' hp (toLocalImage p) hzero
  have hq' : p ≫ q = toLocalImage p := hq
  have hqi : q ≫ (localImage p).ι = 𝟙 P := by
    refine (cancel_epi p).mp ?_
    rw [← Category.assoc, hq', toLocalImage_comp_ι, Category.comp_id]
  have hsplit : IsSplitEpi (localImage p).ι := ⟨⟨q, hqi⟩⟩
  have hiso : IsIso (localImage p).ι := isIso_of_mono_of_isSplitEpi _
  refine ⟨fun {X} x ↦ ?_⟩
  have hyx : (Hom.app (inv (localImage p).ι).val (op X) x).val = x :=
    congrArg (fun ψ : P ⟶ P ↦ Hom.app ψ.val (op X) x) (IsIso.inv_hom_id (localImage p).ι)
  have hy : imageSieveOfHom p (Hom.app (inv (localImage p).ι).val (op X) x).val ∈ J X :=
    (mem_localImage p _).1 (Hom.app (inv (localImage p).ι).val (op X) x).property
  exact hyx ▸ hy

end LocalImage

open Sectionwise LocalImage

/-! ### Sections killed by a morphism whose kernel is given -/

section Exactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- If `φ` is a kernel of `p`, then every section killed by `p` is the image of a section
of the source of `φ`. -/
theorem exists_app_eq_of_isLimit {M N P : SheafOfModules.{m} R} {φ : M ⟶ N} {p : N ⟶ P}
    (hz : φ ≫ p = 0) (hφ : IsLimit (KernelFork.ofι φ hz)) (X : Cᵒᵖ) (x : N.val.obj X)
    (hx : Hom.app p.val X x = 0) : ∃ y : M.val.obj X, Hom.app φ.val X y = x := by
  obtain ⟨q, hq⟩ := KernelFork.IsLimit.lift' hφ (_root_.SheafOfModules.kerIota p)
    (_root_.SheafOfModules.kerIota_comp p)
  refine ⟨Hom.app q.val X ⟨x, (_root_.SheafOfModules.mem_kerSubmodule p X x).2 hx⟩, ?_⟩
  exact congrArg
    (fun ψ : _root_.SheafOfModules.kerObj p ⟶ N ↦ Hom.app ψ.val X
      ⟨x, (_root_.SheafOfModules.mem_kerSubmodule p X x).2 hx⟩) hq

/-- A morphism of presheaves of modules commutes with linear combinations. -/
private theorem app_sum_smul {M N : PresheafOfModules.{m} R.obj} (φ : M ⟶ N) (X : Cᵒᵖ) {n : ℕ}
    (a : Fin n → R.obj.obj X) (x : Fin n → M.obj X) :
    Hom.app φ X (∑ i, a i • x i) = ∑ i, a i • Hom.app φ X (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hom_app_smul φ X (a i) _

/-- A morphism of presheaves of modules commutes with restricted linear combinations. -/
private theorem app_sum_smul_restrict {M N : PresheafOfModules.{m} R.obj} (φ : M ⟶ N) {U V : C}
    (h : V ⟶ U) {n : ℕ} (a : Fin n → R.obj.obj (op V)) (x : Fin n → M.obj (op U)) :
    Hom.app φ (op V) (∑ i, a i • M.restrictₛₗ h.op (x i))
      = ∑ i, a i • N.restrictₛₗ h.op (Hom.app φ (op U) (x i)) :=
  (app_sum_smul φ _ a _).trans (Finset.sum_congr rfl fun i _ ↦
    congrArg (fun z ↦ a i • z) (PresheafOfModules.naturality_apply φ h.op (x i)))

end Exactness

/-! ### The sectionwise form of Stacks 01B7: finite type of a middle term -/

section Middle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The sieve of arrows along which each of finitely many sections of the target of a morphism
of sheaves of modules lifts: the intersection of the individual image sieves. -/
noncomputable def commonLiftSieve {X₂ X₃ : SheafOfModules.{m} R} (p : X₂ ⟶ X₃) {U : C} :
    (n : ℕ) → (Fin n → X₃.val.obj (op U)) → Sieve U
  | 0, _ => ⊤
  | n + 1, s => imageSieveOfHom p (s 0) ⊓ commonLiftSieve p n (fun i ↦ s i.succ)

/-- The common lift sieve of a locally surjective morphism is a covering sieve. -/
theorem commonLiftSieve_mem {X₂ X₃ : SheafOfModules.{m} R} (p : X₂ ⟶ X₃)
    (hp : PresheafOfModules.IsLocallySurjective J p.val) {U : C} (n : ℕ)
    (s : Fin n → X₃.val.obj (op U)) : commonLiftSieve p n s ∈ J U := by
  have := hp
  induction n with
  | zero => exact J.top_mem U
  | succ n ih =>
      exact J.intersection_covering
        (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map p.val) (s 0))
        (ih (fun i ↦ s i.succ))

/-- On the common lift sieve each of the given sections lifts. -/
theorem commonLiftSieve_le {X₂ X₃ : SheafOfModules.{m} R} (p : X₂ ⟶ X₃) {U : C} (n : ℕ)
    (s : Fin n → X₃.val.obj (op U)) (i : Fin n) :
    commonLiftSieve p n s ≤ imageSieveOfHom p (s i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      intro V f hf
      rcases i with ⟨i, hi⟩
      simp only [commonLiftSieve] at hf ⊢
      rcases i with _ | i
      · exact hf.1
      · exact ih (fun j ↦ s j.succ) ⟨i, by lia⟩ f hf.2

/-- Let `ι` be a kernel of `p`.  If
over an object `U` the source of `ι` has a finite generating family `s₁`, the target of `p` has
a finite generating family `s₃`, and each member of `s₃` lifts to a section `b i` of the middle
term, then the images of `s₁` together with the lifts `b` generate the middle term over `U`. -/
theorem generates_middle_of_lifts {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂} {p : X₂ ⟶ X₃}
    (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz)) {U : C} {n₁ n₃ : ℕ}
    (s₁ : Fin n₁ → X₁.val.obj (op U)) (s₃ : Fin n₃ → X₃.val.obj (op U))
    (b : Fin n₃ → X₂.val.obj (op U)) (hs₁ : Generates J X₁.val s₁)
    (hs₃ : Generates J X₃.val s₃) (hb : ∀ i, Hom.app p.val (op U) (b i) = s₃ i) :
    Generates J X₂.val (Fin.append (fun i ↦ Hom.app ι.val (op U) (s₁ i)) b) := by
  let s₂ : Fin (n₁ + n₃) → X₂.val.obj (op U) :=
    Fin.append (fun i ↦ Hom.app ι.val (op U) (s₁ i)) b
  show Generates J X₂.val s₂
  intro V f t
  let S : Sieve V :=
    { arrows := fun W g ↦ ∃ a : Fin (n₁ + n₃) → R.obj.obj (op W),
        ∑ i, a i • X₂.val.restrictₛₗ (g ≫ f).op (s₂ i) = X₂.val.restrictₛₗ g.op t
      downward_closed := by
        intro W Z g hg k
        obtain ⟨a, ha⟩ := hg
        refine ⟨fun i ↦ R.obj.map k.op (a i), ?_⟩
        have hh := congrArg (X₂.val.restrictₛₗ k.op) ha
        rw [restrict_sum_smul] at hh
        refine Eq.trans (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ ?_))
          (hh.trans (restrict_restrict g k t))
        refine congrArg (fun z ↦ R.obj.map k.op (a i) • z) ?_
        exact (restrict_restrict_eq (g ≫ f) k ((k ≫ g) ≫ f)
          (by simp only [Category.assoc]) (s₂ i)).symm }
  refine ⟨S, ?_, fun W g hg ↦ hg⟩
  obtain ⟨S₃, hS₃, hgen₃⟩ := hs₃ V f (Hom.app p.val (op V) t)
  refine J.transitive hS₃ S (fun W g hg ↦ ?_)
  obtain ⟨c, hc⟩ := hgen₃ W g hg
  have hsum : Hom.app p.val (op W) (∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i))
      = ∑ i, c i • X₃.val.restrictₛₗ (g ≫ f).op (s₃ i) :=
    (app_sum_smul_restrict p.val (g ≫ f) c b).trans (by simp only [hb])
  have hzero : Hom.app p.val (op W)
      (X₂.val.restrictₛₗ g.op t - ∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i)) = 0 := by
    refine (map_sub (ConcreteCategory.hom (Hom.app p.val (op W))) _ _).trans ?_
    rw [hsum, show Hom.app p.val (op W) (X₂.val.restrictₛₗ g.op t)
      = X₃.val.restrictₛₗ g.op (Hom.app p.val (op V) t) from
        PresheafOfModules.naturality_apply p.val g.op t, hc]
    exact sub_self _
  obtain ⟨y, hy⟩ := exists_app_eq_of_isLimit hz hι (op W) _ hzero
  obtain ⟨S₁, hS₁, hgen₁⟩ := hs₁ W (g ≫ f) y
  refine J.superset_covering (fun Z k hk ↦ ?_) hS₁
  obtain ⟨d, hd⟩ := hgen₁ Z k hk
  show S.arrows (k ≫ g)
  refine ⟨Fin.append d (fun i ↦ R.obj.map k.op (c i)), ?_⟩
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hleft : (∑ i, d i • X₂.val.restrictₛₗ ((k ≫ g) ≫ f).op (Hom.app ι.val (op U) (s₁ i)))
      = Hom.app ι.val (op Z) (X₁.val.restrictₛₗ k.op y) :=
    (app_sum_smul_restrict ι.val ((k ≫ g) ≫ f) d s₁).symm.trans
      (congrArg (Hom.app ι.val (op Z)) (by rw [Category.assoc]; exact hd))
  have hright : (∑ i, R.obj.map k.op (c i) • X₂.val.restrictₛₗ ((k ≫ g) ≫ f).op (b i))
      = X₂.val.restrictₛₗ k.op (∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i)) := by
    refine Eq.trans (Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦
      congrArg (fun z ↦ R.obj.map k.op (c i) • z) ?_))
      (restrict_sum_smul k c (fun i ↦ X₂.val.restrictₛₗ (g ≫ f).op (b i))).symm
    exact (restrict_restrict_eq (g ≫ f) k ((k ≫ g) ≫ f)
      (by simp only [Category.assoc]) (b i)).symm
  have hy2 : Hom.app ι.val (op Z) (X₁.val.restrictₛₗ k.op y)
      = X₂.val.restrictₛₗ (k ≫ g).op t
        - X₂.val.restrictₛₗ k.op (∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i)) := by
    refine (PresheafOfModules.naturality_apply ι.val k.op y).trans ?_
    refine (congrArg (X₂.val.restrictₛₗ k.op) hy).trans ?_
    refine (map_sub (X₂.val.restrictₛₗ k.op) _ _).trans ?_
    exact congrArg (fun z ↦ z - X₂.val.restrictₛₗ k.op
      (∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i))) (restrict_restrict g k t)
  calc (∑ i, d i • X₂.val.restrictₛₗ ((k ≫ g) ≫ f).op (s₂ (Fin.castAdd n₃ i)))
        + (∑ i, R.obj.map k.op (c i) • X₂.val.restrictₛₗ ((k ≫ g) ≫ f).op
            (s₂ (Fin.natAdd n₁ i)))
      = Hom.app ι.val (op Z) (X₁.val.restrictₛₗ k.op y)
        + X₂.val.restrictₛₗ k.op (∑ i, c i • X₂.val.restrictₛₗ (g ≫ f).op (b i)) := by
          simpa only [s₂, Fin.append_left, Fin.append_right]
            using congrArg₂ (· + ·) hleft hright
    _ = X₂.val.restrictₛₗ (k ≫ g).op t := by rw [hy2, sub_add_cancel]

/-- If `ι` is a kernel of `p`, `p` is locally surjective, and the outer terms are of finite type
in the sectionwise sense, then so is the middle term. -/
theorem presheaf_isFiniteType_X₂ {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂} {p : X₂ ⟶ X₃}
    (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    (hp : PresheafOfModules.IsLocallySurjective J p.val)
    (h₁ : PresheafOfModules.IsFiniteType J X₁.val)
    (h₃ : PresheafOfModules.IsFiniteType J X₃.val) :
    PresheafOfModules.IsFiniteType J X₂.val := by
  have hc₁ := coversTop_generates h₁
  have hc₃ := coversTop_generates h₃
  refine ⟨{ V : C // ∃ (n : ℕ) (s : Fin n → X₂.val.obj (op V)), Generates J X₂.val s },
    Subtype.val, fun U ↦ ?_, fun i ↦ i.2⟩
  refine J.transitive (hc₁ U) _ (fun V f hf ↦ ?_)
  obtain ⟨i₁, ⟨g₁⟩⟩ := (Sieve.mem_ofObjects_iff _ f).1 hf
  obtain ⟨n₁, u₁, hu₁⟩ := i₁.2
  have ht₁ : Generates J X₁.val (fun i ↦ X₁.val.restrictₛₗ g₁.op (u₁ i)) :=
    generates_restrict g₁ u₁ hu₁
  refine J.transitive (hc₃ V) _ (fun W g hg ↦ ?_)
  obtain ⟨i₃, ⟨g₃⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  obtain ⟨n₃, u₃, hu₃⟩ := i₃.2
  have ht₃ : Generates J X₃.val (fun i ↦ X₃.val.restrictₛₗ g₃.op (u₃ i)) :=
    generates_restrict g₃ u₃ hu₃
  have ht₁' : Generates J X₁.val
      (fun i ↦ X₁.val.restrictₛₗ g.op (X₁.val.restrictₛₗ g₁.op (u₁ i))) :=
    generates_restrict g _ ht₁
  refine J.transitive (commonLiftSieve_mem p hp n₃
    (fun i ↦ X₃.val.restrictₛₗ g₃.op (u₃ i))) _ (fun Z k hk ↦ ?_)
  have hlift (i : Fin n₃) : ∃ y : X₂.val.obj (op Z), Hom.app p.val (op Z) y
      = X₃.val.restrictₛₗ k.op (X₃.val.restrictₛₗ g₃.op (u₃ i)) :=
    (mem_imageSieveOfHom p (X₃.val.restrictₛₗ g₃.op (u₃ i)) k).1
      (commonLiftSieve_le p n₃ (fun i ↦ X₃.val.restrictₛₗ g₃.op (u₃ i)) i k hk)
  choose b hb using hlift
  have hgen := generates_middle_of_lifts hz hι
    (fun i ↦ X₁.val.restrictₛₗ k.op (X₁.val.restrictₛₗ g.op (X₁.val.restrictₛₗ g₁.op (u₁ i))))
    (fun i ↦ X₃.val.restrictₛₗ k.op (X₃.val.restrictₛₗ g₃.op (u₃ i))) b
    (generates_restrict k _ ht₁') (generates_restrict k _ ht₃) hb
  refine J.superset_covering (S := ⊤) (fun Z' q _ ↦ ?_) (J.top_mem Z)
  exact (Sieve.mem_ofObjects_iff _ q).2 ⟨⟨Z, n₁ + n₃, _, hgen⟩, ⟨q⟩⟩

end Middle

/-! ### Relations among sections of an extension -/

section RelationsExtension

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Iterated restriction of a section of the sheaf of rings is restriction along the
composite. -/
lemma ring_map_map {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (x : R.obj.obj (op X)) :
    R.obj.map g.op (R.obj.map f.op x) = R.obj.map (g ≫ f).op x :=
  (ConcreteCategory.congr_hom (show R.obj.map (g ≫ f).op
    = R.obj.map f.op ≫ R.obj.map g.op by rw [op_comp, R.obj.map_comp]) x).symm

/-- Restriction of a sum of products of sections of the sheaf of rings. -/
lemma ring_map_sum_mul {X Y : Cᵒᵖ} (f : X ⟶ Y) {q : ℕ} (a b : Fin q → R.obj.obj X) :
    R.obj.map f (∑ l, a l * b l) = ∑ l, R.obj.map f (a l) * R.obj.map f (b l) :=
  (map_sum (ConcreteCategory.hom (R.obj.map f)) (fun l ↦ a l * b l) Finset.univ).trans
    (Finset.sum_congr rfl fun l _ ↦ map_mul (ConcreteCategory.hom (R.obj.map f)) (a l) (b l))

/-- A tuple of coefficients killing a finite family of sections of `X₂` kills their images in
`X₃`: a relation among the family is a relation among the images. -/
theorem mem_relations_imageSections {X₂ X₃ : SheafOfModules.{m} R} (p : X₂ ⟶ X₃) {U : C}
    {n : ℕ} (s : Fin n → X₂.val.obj (op U)) (V : Over U)
    (τ : (relations X₂.val s).obj (op V)) :
    τ.val ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op V.left))
      (fun i ↦ X₃.val.restrictₛₗ V.hom.op (imageSections p s i))) := by
  have hτ := τ.property
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hτ
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  exact (app_sum_smul_restrict p.val V.hom τ.val s).symm.trans
    ((congrArg (Hom.app p.val (op V.left)) hτ).trans (map_zero _))

/-- For a relation among the images in `X₃` of a finite family of sections of `X₂`, the
corresponding linear combination of the family is the image under the kernel `ι` of a section of
`X₁`. -/
theorem exists_app_eq_sum_smul_of_relation {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂}
    {p : X₂ ⟶ X₃} (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz)) {U : C} {n : ℕ}
    (s : Fin n → X₂.val.obj (op U)) (W : Over U)
    (ρ : (relations X₃.val (imageSections p s)).obj (op W)) :
    ∃ y : X₁.val.obj (op W.left),
      Hom.app ι.val (op W.left) y = ∑ i, ρ.val i • X₂.val.restrictₛₗ W.hom.op (s i) := by
  refine exists_app_eq_of_isLimit hz hι (op W.left) _ ?_
  have hp := ρ.property
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hp
  exact (app_sum_smul_restrict p.val W.hom ρ.val s).trans hp

/-- The combination of a finite family of sections of `X₂` with the coefficients of a relation
among their images in `X₃`, restricted along an arrow of the site, is the image under `ι` of the
restriction of the section of `X₁` lifting that relation. -/
theorem app_restrict_lift {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂} {p : X₂ ⟶ X₃}
    {U : C} {n : ℕ} (s : Fin n → X₂.val.obj (op U)) {W : Over U}
    (ρ : (relations X₃.val (imageSections p s)).obj (op W)) (y : X₁.val.obj (op W.left))
    (hy : Hom.app ι.val (op W.left) y = ∑ i, ρ.val i • X₂.val.restrictₛₗ W.hom.op (s i))
    {V : C} (g : V ⟶ W.left) (h : V ⟶ U) (hh : g ≫ W.hom = h) :
    Hom.app ι.val (op V) (X₁.val.restrictₛₗ g.op y)
      = ∑ i, R.obj.map g.op (ρ.val i) • X₂.val.restrictₛₗ h.op (s i) :=
  ((PresheafOfModules.naturality_apply ι.val g.op y).trans
    (congrArg (X₂.val.restrictₛₗ g.op) hy)).trans
    ((restrict_sum_smul g (fun i ↦ ρ.val i) (fun i ↦ X₂.val.restrictₛₗ W.hom.op (s i))).trans
      (Finset.sum_congr rfl fun i _ ↦ congrArg (fun z ↦ R.obj.map g.op (ρ.val i) • z)
        (restrict_restrict_eq W.hom g h hh (s i))))

/-- Let `ι` be a kernel of `p` and let `s` be
a finite family of sections of the middle term over `U`.  Suppose that a finite family `r` of
relations among the images of `s` in `X₃` generates the relations among those images over an
object `W` of the slice site at `U`; let `y` be sections of `X₁` whose images under `ι` are the
combinations of `s` with the coefficients of `r`; and suppose that a finite family `c` of
relations among `y` generates the relations among `y` over an object `Z` of the slice site at
`W.left`.  Then the combinations of `r` with the coefficients of `c` are relations among `s`
over `Z` read above `U`, and they generate the relations among `s`. -/
theorem generates_relations_middle {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂} {p : X₂ ⟶ X₃}
    (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz)) {U : C} {n : ℕ}
    (s : Fin n → X₂.val.obj (op U)) {W : Over U} {P : ℕ}
    (r : Fin P → (relations X₃.val (imageSections p s)).obj (op W))
    (hr : Generates (J.over U) (relations X₃.val (imageSections p s)) r)
    (y : Fin P → X₁.val.obj (op W.left))
    (hy : ∀ l, Hom.app ι.val (op W.left) (y l)
      = ∑ i, (r l).val i • X₂.val.restrictₛₗ W.hom.op (s i))
    {Z : Over W.left} {Q : ℕ} (c : Fin Q → (relations X₁.val y).obj (op Z))
    (hc : Generates (J.over W.left) (relations X₁.val y) c) :
    ∃ ρ : Fin Q → (relations X₂.val s).obj (op (Over.mk (Z.hom ≫ W.hom))),
      Generates (J.over U) (relations X₂.val s) ρ := by
  have : Mono ι := mono_of_isLimit_fork hι
  have hinj : ∀ X : Cᵒᵖ, Function.Injective (Hom.app ι.val X) := injective_val_of_mono ι
  have hmem : ∀ j : Fin Q, (fun i ↦ ∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i))
      ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op Z.left))
        (fun i ↦ X₂.val.restrictₛₗ (Z.hom ≫ W.hom).op (s i))) := by
    intro j
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    have hcj := (c j).property
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hcj
    calc (∑ i, (∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i)) •
            X₂.val.restrictₛₗ (Z.hom ≫ W.hom).op (s i))
        = ∑ l, (c j).val l • (∑ i, R.obj.map Z.hom.op ((r l).val i) •
            X₂.val.restrictₛₗ (Z.hom ≫ W.hom).op (s i)) :=
          (sum_smul_sum_smul_of_fin (fun l ↦ (c j).val l)
            (fun l i ↦ R.obj.map Z.hom.op ((r l).val i))
            (fun i ↦ X₂.val.restrictₛₗ (Z.hom ≫ W.hom).op (s i))).symm
      _ = ∑ l, (c j).val l • Hom.app ι.val (op Z.left) (X₁.val.restrictₛₗ Z.hom.op (y l)) :=
          Finset.sum_congr rfl fun l _ ↦ congrArg (fun z ↦ (c j).val l • z)
            (app_restrict_lift s (r l) (y l) (hy l) Z.hom (Z.hom ≫ W.hom) rfl).symm
      _ = Hom.app ι.val (op Z.left) (∑ l, (c j).val l • X₁.val.restrictₛₗ Z.hom.op (y l)) :=
          (app_sum_smul ι.val (op Z.left) _ _).symm
      _ = 0 := (congrArg (Hom.app ι.val (op Z.left)) hcj).trans (map_zero _)
  refine ⟨fun j ↦ ⟨fun i ↦ ∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i), hmem j⟩,
    generates_of_bind _ fun V f τ ↦ ?_⟩
  let θ : Over.mk (Z.hom ≫ W.hom) ⟶ W := Over.homMk Z.hom rfl
  have hθ : θ.left = Z.hom := rfl
  obtain ⟨S₁, hS₁, hgen₁⟩ := hr V (f ≫ θ) ⟨τ.val, mem_relations_imageSections p s V τ⟩
  refine ⟨S₁, hS₁, fun V₁ g hg ↦ ?_⟩
  obtain ⟨e, he⟩ := hgen₁ V₁ g hg
  let e' : Fin P → R.obj.obj (op V₁.left) := fun l ↦ e l
  have hq : (g ≫ f ≫ θ).left = (g ≫ f).left ≫ Z.hom := by
    rw [Over.comp_left, Over.comp_left, Over.comp_left, hθ, Category.assoc]
  have hcoeff : ∀ i, (∑ l, e' l * R.obj.map (g ≫ f ≫ θ).left.op ((r l).val i))
      = R.obj.map g.left.op (τ.val i) := fun i ↦
    (Finset.sum_congr rfl fun l _ ↦ congrArg (fun z ↦ e' l * z)
        (relations_map_apply_val (imageSections p s) (g ≫ f ≫ θ) (r l) i).symm).trans
      ((coe_sum_smul_apply e _ i).symm.trans ((congrFun (Subtype.ext_iff.1 he) i).trans
        (relations_map_apply_val (imageSections p s) g _ i)))
  have hτ := τ.property
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hτ
  have hzero : Hom.app ι.val (op V₁.left)
      (∑ l, e' l • X₁.val.restrictₛₗ (g ≫ f ≫ θ).left.op (y l)) = 0 :=
    calc Hom.app ι.val (op V₁.left)
            (∑ l, e' l • X₁.val.restrictₛₗ (g ≫ f ≫ θ).left.op (y l))
        = ∑ l, e' l • Hom.app ι.val (op V₁.left)
            (X₁.val.restrictₛₗ (g ≫ f ≫ θ).left.op (y l)) :=
          app_sum_smul ι.val (op V₁.left) _ _
      _ = ∑ l, e' l • (∑ i, R.obj.map (g ≫ f ≫ θ).left.op ((r l).val i) •
            X₂.val.restrictₛₗ V₁.hom.op (s i)) :=
          Finset.sum_congr rfl fun l _ ↦ congrArg (fun z ↦ e' l • z)
            (app_restrict_lift s (r l) (y l) (hy l) (g ≫ f ≫ θ).left V₁.hom
              (Over.w (g ≫ f ≫ θ)))
      _ = ∑ i, (∑ l, e' l * R.obj.map (g ≫ f ≫ θ).left.op ((r l).val i)) •
            X₂.val.restrictₛₗ V₁.hom.op (s i) := sum_smul_sum_smul_of_fin _ _ _
      _ = ∑ i, R.obj.map g.left.op (τ.val i) • X₂.val.restrictₛₗ V₁.hom.op (s i) :=
          Finset.sum_congr rfl fun i _ ↦
            congrArg (fun z ↦ z • X₂.val.restrictₛₗ V₁.hom.op (s i)) (hcoeff i)
      _ = X₂.val.restrictₛₗ g.left.op (∑ i, τ.val i • X₂.val.restrictₛₗ V.hom.op (s i)) :=
          ((restrict_sum_smul g.left (fun i ↦ τ.val i)
            (fun i ↦ X₂.val.restrictₛₗ V.hom.op (s i))).trans
            (Finset.sum_congr rfl fun i _ ↦
              congrArg (fun z ↦ R.obj.map g.left.op (τ.val i) • z)
                (restrict_restrict_eq V.hom g.left V₁.hom (Over.w g) (s i)))).symm
      _ = 0 := (congrArg (X₂.val.restrictₛₗ g.left.op) hτ).trans (map_zero _)
  have hmeme : e' ∈ LinearMap.ker (Fintype.linearCombination (R.obj.obj (op V₁.left))
      (fun l ↦ X₁.val.restrictₛₗ (g ≫ f ≫ θ).left.op (y l))) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact hinj (op V₁.left) (hzero.trans (map_zero _).symm)
  let κ : Over.mk ((g ≫ f ≫ θ).left) ⟶ Z := Over.homMk ((g ≫ f).left) hq.symm
  obtain ⟨S₂, hS₂, hgen₂⟩ := hc (Over.mk ((g ≫ f ≫ θ).left)) κ ⟨e', hmeme⟩
  refine ⟨(Sieve.overEquiv V₁).symm
      (Sieve.overEquiv (Over.mk ((g ≫ f ≫ θ).left)) S₂),
    J.overEquiv_symm_mem_over V₁ _ ((J.mem_over_iff S₂).1 hS₂), fun V₂ k hk ↦ ?_⟩
  let κ₂ : Over.mk (k.left ≫ (g ≫ f ≫ θ).left) ⟶ Over.mk ((g ≫ f ≫ θ).left) :=
    Over.homMk k.left rfl
  obtain ⟨d, hd⟩ := hgen₂ (Over.mk (k.left ≫ (g ≫ f ≫ θ).left)) κ₂
    ((Sieve.overEquiv_iff S₂ k.left).1 ((Sieve.overEquiv_symm_iff _ k).1 hk))
  let d' : Fin Q → R.obj.obj (op V₂.left) := fun j ↦ d j
  let ν : V₂.left ⟶ Z.left := k.left ≫ (g ≫ f).left
  have hν : (κ₂ ≫ κ).left = ν := by
    simp only [κ₂, κ, ν, Over.comp_left, Over.homMk_left]
  have hdcoeff : ∀ l, (∑ j, d' j * R.obj.map ν.op ((c j).val l))
      = R.obj.map k.left.op (e' l) := fun l ↦
    (Finset.sum_congr rfl fun j _ ↦ congrArg (fun z ↦ d' j * z)
        (((relations_map_apply_val y (κ₂ ≫ κ) (c j) l).trans
          (congrArg (fun h : V₂.left ⟶ Z.left ↦ R.obj.map h.op ((c j).val l)) hν)).symm)).trans
      ((coe_sum_smul_apply d' _ l).symm.trans ((congrFun (Subtype.ext_iff.1 hd) l).trans
        (relations_map_apply_val y κ₂ _ l)))
  have hμ : ((k ≫ g) ≫ f).left = ν := by
    simp only [ν, Over.comp_left, Category.assoc]
  have hcomp : ν ≫ Z.hom = k.left ≫ (g ≫ f ≫ θ).left := by
    rw [hq]
    simp only [ν, Over.comp_left, Category.assoc]
  refine ⟨d', Subtype.ext (funext fun i ↦ ?_)⟩
  have hstep : ∀ j : Fin Q,
      R.obj.map ν.op (∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i))
        = ∑ l, R.obj.map ν.op ((c j).val l) *
            R.obj.map (k.left ≫ (g ≫ f ≫ θ).left).op ((r l).val i) := fun j ↦
    (ring_map_sum_mul _ _ _).trans (Finset.sum_congr rfl fun l _ ↦
      congrArg (fun z ↦ R.obj.map ν.op ((c j).val l) * z)
        ((ring_map_map Z.hom ν ((r l).val i)).trans
          (congrArg (fun h : V₂.left ⟶ W.left ↦ R.obj.map h.op ((r l).val i)) hcomp)))
  calc ((∑ j, d' j • (relations X₂.val s).restrictₛₗ ((k ≫ g) ≫ f).op
            (⟨fun i ↦ ∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i), hmem j⟩ :
              (relations X₂.val s).obj (op (Over.mk (Z.hom ≫ W.hom))))).val i)
      = ∑ j, d' j * R.obj.map ν.op
          (∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i)) :=
        (coe_sum_smul_apply d' _ i).trans (Finset.sum_congr rfl fun j _ ↦
          congrArg (fun z ↦ d' j * z)
            ((relations_map_apply_val s ((k ≫ g) ≫ f) _ i).trans
              (congrArg (fun h : V₂.left ⟶ Z.left ↦ R.obj.map h.op
                (∑ l, (c j).val l * R.obj.map Z.hom.op ((r l).val i))) hμ)))
    _ = ∑ j, ∑ l, d' j * (R.obj.map ν.op ((c j).val l) *
          R.obj.map (k.left ≫ (g ≫ f ≫ θ).left).op ((r l).val i)) := by
        simp only [hstep, Finset.mul_sum]
    _ = ∑ l, (∑ j, d' j * R.obj.map ν.op ((c j).val l)) *
          R.obj.map (k.left ≫ (g ≫ f ≫ θ).left).op ((r l).val i) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ l, R.obj.map k.left.op (e' l) *
          R.obj.map (k.left ≫ (g ≫ f ≫ θ).left).op ((r l).val i) :=
        Finset.sum_congr rfl fun l _ ↦ congrArg
          (fun z ↦ z * R.obj.map (k.left ≫ (g ≫ f ≫ θ).left).op ((r l).val i)) (hdcoeff l)
    _ = R.obj.map k.left.op (∑ l, e' l * R.obj.map (g ≫ f ≫ θ).left.op ((r l).val i)) :=
        ((ring_map_sum_mul k.left.op (fun l ↦ e' l)
          (fun l ↦ R.obj.map (g ≫ f ≫ θ).left.op ((r l).val i))).trans
          (Finset.sum_congr rfl fun l _ ↦ congrArg
            (fun z ↦ R.obj.map k.left.op (e' l) * z)
            (ring_map_map (g ≫ f ≫ θ).left k.left ((r l).val i)))).symm
    _ = R.obj.map k.left.op (R.obj.map g.left.op (τ.val i)) :=
        congrArg (R.obj.map k.left.op) (hcoeff i)
    _ = ((relations X₂.val s).restrictₛₗ (k ≫ g).op τ).val i :=
        (ring_map_map g.left k.left (τ.val i)).trans
          ((congrArg (fun h : V₂.left ⟶ V.left ↦ R.obj.map h.op (τ.val i))
            (show k.left ≫ g.left = (k ≫ g).left by simp only [Over.comp_left])).trans
            (relations_map_apply_val s (k ≫ g) τ i).symm)

/-- If `ι` is a kernel of `p` and the outer terms are coherent, then the relations among any
finite family of sections of the middle term are of finite type. -/
theorem presheaf_isFiniteType_relations_X₂ {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂}
    {p : X₂ ⟶ X₃} (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    (h₁ : IsCoherentOnSite X₁) (h₃ : IsCoherentOnSite X₃)
    (U : C) (n : ℕ) (s : Fin n → X₂.val.obj (op U)) :
    PresheafOfModules.IsFiniteType (J.over U) (relations X₂.val s) := by
  have hc₃ := coversTop_generates (h₃.kernel_isFiniteType U n (imageSections p s))
  refine ⟨{ V : Over U // ∃ (Q : ℕ) (ρ : Fin Q → (relations X₂.val s).obj (op V)),
      Generates (J.over U) (relations X₂.val s) ρ }, Subtype.val, fun W₀ ↦ ?_, fun i ↦ i.2⟩
  refine (J.over U).transitive (hc₃ W₀) _ (fun W θ hθ ↦ ?_)
  obtain ⟨i₃, ⟨g₃⟩⟩ := (Sieve.mem_ofObjects_iff _ θ).1 hθ
  obtain ⟨P, r₀, hr₀⟩ := i₃.2
  have hr : Generates (J.over U) (relations X₃.val (imageSections p s))
      (fun l ↦ (relations X₃.val (imageSections p s)).restrictₛₗ g₃.op (r₀ l)) :=
    generates_restrict g₃ r₀ hr₀
  choose y hy using fun l ↦ exists_app_eq_sum_smul_of_relation hz hι s W
    ((relations X₃.val (imageSections p s)).restrictₛₗ g₃.op (r₀ l))
  have hcZ := coversTop_generates (h₁.kernel_isFiniteType W.left P y)
  have hcZ₀ := hcZ (Over.mk (𝟙 W.left))
  rw [J.mem_over_iff] at hcZ₀
  refine (J.over U).transitive (J.overEquiv_symm_mem_over W _ hcZ₀) _ (fun V₃ θ₃ hθ₃ ↦ ?_)
  rw [Sieve.overEquiv_symm_iff, Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff] at hθ₃
  obtain ⟨iZ, ⟨η⟩⟩ := hθ₃
  obtain ⟨Q, c₀, hc₀⟩ := iZ.2
  obtain ⟨ρ, hρ⟩ := generates_relations_middle hz hι s _ hr y hy
    (fun j ↦ (relations X₁.val y).restrictₛₗ η.op (c₀ j)) (generates_restrict η c₀ hc₀)
  refine (J.over U).superset_covering (S := ⊤) (fun V₄ κ _ ↦ ?_) ((J.over U).top_mem V₃)
  refine (Sieve.mem_ofObjects_iff _ _).2
    ⟨⟨Over.mk ((Over.mk (θ₃.left ≫ 𝟙 W.left)).hom ≫ W.hom), Q, ρ, hρ⟩, ⟨κ ≫ ?_⟩⟩
  exact Over.homMk (𝟙 V₃.left) (by
    simp only [Over.mk_left, Over.mk_hom, Category.id_comp, Category.comp_id]
    exact Over.w θ₃)

end RelationsExtension

/-! ### Extensions of coherent sheaves of modules -/

section Closure

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- If `ι` is a kernel of `p`, `p` is locally surjective, and the outer terms are coherent, then
the middle term is coherent. -/
theorem isCoherentOnSite_middle {X₁ X₂ X₃ : SheafOfModules.{m} R} {ι : X₁ ⟶ X₂} {p : X₂ ⟶ X₃}
    (hz : ι ≫ p = 0) (hι : IsLimit (KernelFork.ofι ι hz))
    (hp : PresheafOfModules.IsLocallySurjective J p.val)
    (h₁ : IsCoherentOnSite X₁) (h₃ : IsCoherentOnSite X₃) : IsCoherentOnSite X₂ where
  isFiniteType := presheaf_isFiniteType_X₂ hz hι hp h₁.isFiniteType h₃.isFiniteType
  kernel_isFiniteType := presheaf_isFiniteType_relations_X₂ hz hι h₁ h₃

/-- An extension of coherent sheaves of modules is coherent: the middle term of a short exact
sequence of sheaves of modules whose outer terms are coherent is coherent. -/
@[ega "0 5.3.3" "partial"]
theorem isCoherentOnSite_X₂_of_shortExact [Balanced (SheafOfModules.{m} R)]
    {T : ShortComplex (SheafOfModules.{m} R)} (hT : T.ShortExact)
    (h₁ : IsCoherentOnSite T.X₁) (h₃ : IsCoherentOnSite T.X₃) :
    IsCoherentOnSite T.X₂ :=
  isCoherentOnSite_middle T.zero hT.fIsKernel
    (isLocallySurjective_of_isColimit T.zero hT.gIsCokernel) h₁ h₃

end Closure

end Stacks.SheafOfModules

end
