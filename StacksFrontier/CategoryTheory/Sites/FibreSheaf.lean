module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.OverMapConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# The fibre of a morphism of abelian sheaves over a global section

Let `g : A ⟶ B` be a morphism of abelian sheaves on a site with a terminal object `T`, and let
`s` be a global section of `B`. The sections `t` of `A` with `g(t) = s` form a sheaf of sets
`fibreSheaf g hT s`, a subsheaf of the underlying sheaf of sets of `A`. Translation by a global
section of the kernel of `g` acts on it, and when `g` is an epimorphism and `φ : K ⟶ A` is a
kernel of `g`, it is locally isomorphic to the underlying sheaf of sets of `K`: over an object
`V` on which it has a section `t₀`, translation by `t₀` identifies the restriction of `K` to the
localized site at `V` with that of the fibre. In particular, for `K` the constant sheaf on a
finite abelian group the fibre is a finite locally constant sheaf of sets.

This is the torsor attached to the boundary of `s` in the proof of
[Stacks, Tag 03AJ]: the class of the torsor `fibreSheaf g hT s` is `∂ s ∈ H^1(K)`.

## Main definitions

* `Stacks.FibreSheaf.subfunctor` and `Stacks.FibreSheaf.fibreSheaf` — the fibre.
* `Stacks.FibreSheaf.translate` — translation by a global section of the kernel.
* `Stacks.FibreSheaf.overIso` — the local trivialization over an object carrying a section.

## Main results

* `Stacks.FibreSheaf.exists_covering_nonempty` — an epimorphism makes the fibre locally
  nonempty.
* `Stacks.FibreSheaf.isFiniteLocallyConstant` — the fibre over a section of an epimorphism with
  finite constant kernel is finite locally constant.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.FibreSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A B : Sheaf J AddCommGrpCat.{w}} (g : A ⟶ B) {T : C} (hT : IsTerminal T)
  (s : B.obj.obj (op T))

/-- The restriction of a global section to an object. -/
abbrev restr {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (x : F.obj (op T)) (U : C) : F.obj (op U) :=
  F.map (hT.from U).op x

/-- Restricting the restriction of a global section to `U` along `V ⟶ U` gives its restriction to
`V`. -/
theorem restr_map {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (x : F.obj (op T)) {U V : C} (i : V ⟶ U) :
    F.map i.op (restr hT x U) = restr hT x V := by
  rw [restr, restr, ← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
    hT.hom_ext (i ≫ hT.from U) (hT.from V)]

/-- A section of the underlying presheaf of sets of `A`, read as a section of `A`. -/
abbrev toSec {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {U : Cᵒᵖ} (t : (F ⋙ forget AddCommGrpCat.{w}).obj U) :
    F.obj U :=
  t

/-- A section of `A`, read as a section of the underlying presheaf of sets of `A`. -/
abbrev ofSec {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {U : Cᵒᵖ} (t : F.obj U) :
    (F ⋙ forget AddCommGrpCat.{w}).obj U :=
  t

/-- The restriction of a global section is compatible with the maps of the presheaf. -/
theorem restr_map' {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (x : F.obj (op T)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    F.map i (restr hT x U.unop) = restr hT x V.unop :=
  restr_map hT x i.unop

/-- The sections of `A` lying over the global section `s` of `B`. -/
def subfunctor : Subfunctor (A.obj ⋙ forget AddCommGrpCat.{w}) where
  obj U := {t | g.hom.app U t = restr hT s U.unop}
  map {U V} i t ht := by
    change g.hom.app V (A.obj.map i t) = restr hT s V.unop
    rw [NatTrans.naturality_apply, show g.hom.app U t = restr hT s U.unop from ht]
    exact restr_map hT s i.unop

/-- A section `t` of `A` lies in the fibre if and only if `g(t)` is the restriction of `s`. -/
theorem mem_subfunctor_obj {U : Cᵒᵖ} (t : A.obj.obj U) :
    t ∈ (subfunctor g hT s).obj U ↔ g.hom.app U t = restr hT s U.unop :=
  Iff.rfl

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The underlying presheaf of sets of an abelian sheaf satisfies the sheaf condition. -/
theorem isSheaf_forget (F : Sheaf J AddCommGrpCat.{w}) :
    Presieve.IsSheaf J (F.obj ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget AddCommGrpCat.{w})).obj F).cond

include g in
/-- The fibre of a morphism of abelian sheaves over a global section satisfies the sheaf
condition: the equation `g(t) = s` can be checked locally, `B` being separated. -/
theorem isSheaf_subfunctor :
    Presieve.IsSheaf J (subfunctor g hT s).toFunctor := by
  refine (Subfunctor.isSheaf_iff _ (isSheaf_forget A)).2 fun U t ht => ?_
  refine ((isSheaf_forget B) _ ht).isSeparatedFor.ext fun V f hf => ?_
  have hf' : g.hom.app (op V) (A.obj.map f.op t) = restr hT s V := hf
  show B.obj.map f.op (g.hom.app U t) = B.obj.map f.op (restr hT s U.unop)
  rw [← NatTrans.naturality_apply, hf', restr_map]

/-- **The fibre sheaf.** The sheaf of sets of sections `t` of `A` with `g(t) = s`. -/
def fibreSheaf : Sheaf J (Type w) :=
  ⟨(subfunctor g hT s).toFunctor, (isSheaf_iff_isSheaf_of_type J _).2 (isSheaf_subfunctor g hT s)⟩

/-! ### Translation by a global section of the kernel -/

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Translation by a global section `a` of `A` with `g(a) = 0` maps the fibre to itself. -/
theorem add_restr_mem {U : Cᵒᵖ} {t : A.obj.obj U} (ht : t ∈ (subfunctor g hT s).obj U)
    (a : A.obj.obj (op T)) (ha : g.hom.app (op T) a = 0) :
    toSec t + restr hT a U.unop ∈ (subfunctor g hT s).obj U := by
  rw [mem_subfunctor_obj] at ht ⊢
  rw [map_add, ht, restr, NatTrans.naturality_apply, ha, map_zero, add_zero]

/-- **Translation** by a global section `a` of the kernel of `g`, as an endomorphism of the fibre
sheaf. -/
def translate (a : A.obj.obj (op T)) (ha : g.hom.app (op T) a = 0) :
    fibreSheaf g hT s ⟶ fibreSheaf g hT s where
  hom :=
    { app U := TypeCat.ofHom fun t =>
        ⟨ofSec (toSec t.1 + restr hT a U.unop), add_restr_mem g hT s t.2 a ha⟩
      naturality U V i := by
        ext t
        refine Subtype.ext ?_
        change A.obj.map i (toSec t.1) + restr hT a V.unop =
          A.obj.map i (toSec t.1 + restr hT a U.unop)
        rw [map_add, restr_map'] }

/-- Translation by `a` sends a section `t` of the fibre to `t + a`. -/
theorem translate_app_coe (a : A.obj.obj (op T)) (ha : g.hom.app (op T) a = 0) (U : Cᵒᵖ)
    (t : (fibreSheaf g hT s).obj.obj U) :
    toSec ((translate g hT s a ha).hom.app U t).1 = toSec t.1 + restr hT a U.unop :=
  rfl

/-- Translation by `a + b` is translation by `a` followed by translation by `b`. -/
theorem translate_add (a b : A.obj.obj (op T)) (ha : g.hom.app (op T) a = 0)
    (hb : g.hom.app (op T) b = 0) :
    translate g hT s (a + b) (by rw [map_add, ha, hb, add_zero]) =
      translate g hT s a ha ≫ translate g hT s b hb := by
  ext U t
  refine Subtype.ext ?_
  show toSec t.1 + restr hT (a + b) U.unop =
    toSec t.1 + restr hT a U.unop + restr hT b U.unop
  rw [restr, map_add, add_assoc]

/-- Translation by `0` is the identity of the fibre sheaf. -/
theorem translate_zero : translate g hT s 0 (map_zero _) = 𝟙 _ := by
  ext U t
  refine Subtype.ext ?_
  show toSec t.1 + restr hT 0 U.unop = t.1
  rw [restr, map_zero, add_zero]

/-- Translation by a global section of the kernel, as an automorphism of the fibre sheaf. -/
def translateIso (a : A.obj.obj (op T)) (ha : g.hom.app (op T) a = 0) :
    fibreSheaf g hT s ≅ fibreSheaf g hT s where
  hom := translate g hT s a ha
  inv := translate g hT s (-a) (by rw [map_neg, ha, neg_zero])
  hom_inv_id := by rw [← translate_add, ← translate_zero]; congr 1; abel
  inv_hom_id := by rw [← translate_add, ← translate_zero]; congr 1; abel

/-! ### Local nonemptiness -/

/-- **The fibre of an epimorphism is locally nonempty**: every object is covered by objects over
which the fibre has a section. -/
theorem exists_covering_nonempty [Sheaf.IsLocallySurjective g] (U : C) :
    Sieve.ofArrows (fun i : (Σ V : C, {_f : V ⟶ U // Nonempty ((fibreSheaf g hT s).obj.obj
        (op V))}) => i.1) (fun i => i.2.1) ∈ J U := by
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J g.hom (restr hT s U))
  intro V f ⟨t, ht⟩
  have hmem : t ∈ (subfunctor g hT s).obj (op V) := by
    show g.hom.app (op V) t = restr hT s V
    rw [ht, restr_map]
  exact Sieve.ofArrows_mk (fun i : (Σ V : C, {f : V ⟶ U // Nonempty ((fibreSheaf g hT s).obj.obj
    (op V))}) => i.1) (fun i => i.2.1) ⟨V, ⟨f, ⟨⟨t, hmem⟩⟩⟩⟩

/-! ### Local triviality -/

section Kernel

variable {K : Sheaf J AddCommGrpCat.{w}} (φ : K ⟶ A)
  (hφ : ∀ U : Cᵒᵖ, Function.Injective (φ.hom.app U))
  (hker : ∀ (U : Cᵒᵖ) (x : A.obj.obj U), g.hom.app U x = 0 → ∃ y, φ.hom.app U y = x)
  (hcomp : φ ≫ g = 0)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
include hcomp in
/-- If `φ ≫ g = 0`, then `g(φ(y)) = 0` for every section `y` of `K`. -/
theorem app_comp_apply_eq_zero (U : Cᵒᵖ) (y : K.obj.obj U) :
    g.hom.app U (φ.hom.app U y) = 0 := by
  have := congrArg (fun h : K ⟶ B => h.hom.app U y) hcomp
  simpa using this

/-- The section of the fibre `t + φ(y)`. -/
def addKernel {U : Cᵒᵖ} (t : (fibreSheaf g hT s).obj.obj U) (y : K.obj.obj U) :
    (fibreSheaf g hT s).obj.obj U :=
  ⟨ofSec (toSec t.1 + φ.hom.app U y), by
    have ht : g.hom.app U (toSec t.1) = restr hT s U.unop := t.2
    change g.hom.app U (toSec t.1 + φ.hom.app U y) = restr hT s U.unop
    rw [map_add, ht, app_comp_apply_eq_zero g φ hcomp, add_zero]⟩

/-- The section `t + φ(y)` of the fibre is compatible with restriction. -/
theorem addKernel_map {U U' : Cᵒᵖ} (h : U ⟶ U') (t : (fibreSheaf g hT s).obj.obj U)
    (y : K.obj.obj U) :
    (fibreSheaf g hT s).obj.map h (addKernel g hT s φ hcomp t y) =
      addKernel g hT s φ hcomp ((fibreSheaf g hT s).obj.map h t) (K.obj.map h y) := by
  refine Subtype.ext ?_
  have hn := NatTrans.naturality_apply φ.hom h y
  show A.obj.map h (toSec t.1 + φ.hom.app U y) =
    A.obj.map h (toSec t.1) + φ.hom.app U' (K.obj.map h y)
  rw [map_add, hn]

include hφ hker in
/-- For a section `t` of the fibre, the map `y ↦ t + φ(y)` from sections of `K` to sections of the
fibre is bijective. -/
theorem addKernel_bijective {U : Cᵒᵖ} (t : (fibreSheaf g hT s).obj.obj U) :
    Function.Bijective (addKernel g hT s φ hcomp t) := by
  refine ⟨fun y y' h => hφ U ?_, fun t' => ?_⟩
  · have := congrArg (fun x : (fibreSheaf g hT s).obj.obj U => toSec x.1) h
    exact add_left_cancel (a := toSec t.1) this
  · have key (u : (fibreSheaf g hT s).obj.obj U) : g.hom.app U (toSec u.1) = restr hT s U.unop :=
      u.2
    obtain ⟨y, hy⟩ := hker U (toSec t'.1 - toSec t.1) (by rw [map_sub, key, key, sub_self])
    refine ⟨y, Subtype.ext ?_⟩
    show toSec t.1 + φ.hom.app U y = toSec t'.1
    rw [hy, add_sub_cancel]

/-- **The local trivialization of the fibre.** Over an object `V` on which the fibre has a
section `t₀`, the map `y ↦ t₀ + φ(y)` identifies the restriction to the localized site at `V` of
the underlying sheaf of sets of `K` with that of the fibre. -/
def overIso (V : C) (t₀ : (fibreSheaf g hT s).obj.obj (op V)) :
    (J.overPullback (Type w) V).obj ((sheafCompose J (forget AddCommGrpCat.{w})).obj K) ≅
      (J.overPullback (Type w) V).obj (fibreSheaf g hT s) :=
  (fullyFaithfulSheafToPresheaf (J.over V) (Type w)).preimageIso
    (NatIso.ofComponents (fun W => (Equiv.ofBijective _ (addKernel_bijective g hT s φ hφ hker hcomp
      ((fibreSheaf g hT s).obj.map W.unop.hom.op t₀))).toIso) (by
        intro W W' i
        ext y
        change addKernel g hT s φ hcomp ((fibreSheaf g hT s).obj.map W'.unop.hom.op t₀)
            (K.obj.map i.unop.left.op y) =
          (fibreSheaf g hT s).obj.map i.unop.left.op
            (addKernel g hT s φ hcomp ((fibreSheaf g hT s).obj.map W.unop.hom.op t₀) y)
        refine Eq.trans ?_ (addKernel_map g hT s φ hcomp i.unop.left.op _ y).symm
        refine congrArg (fun t => addKernel g hT s φ hcomp t (K.obj.map i.unop.left.op y)) ?_
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w i.unop]))

end Kernel

/-! ### Finite local constancy -/

section Constant

variable [HasBinaryProducts C] [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.PreservesSheafification (forget AddCommGrpCat.{w})]
  [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- **The fibre over a global section of an epimorphism with finite constant kernel is finite
locally constant.** Let `φ : M_C ⟶ A` be a kernel of `g : A ⟶ B` (sectionwise injective, with image
the sectionwise kernel of `g`), where `M_C` is the constant sheaf on a finite abelian group `M`,
and let `g` be locally surjective. Then the fibre of `g` over every global section of `B` is a
finite locally constant sheaf of sets. -/
theorem isFiniteLocallyConstant [Sheaf.IsLocallySurjective g] (M : AddCommGrpCat.{w}) [Finite M]
    (φ : (constantSheaf J AddCommGrpCat.{w}).obj M ⟶ A)
    (hφ : ∀ U : Cᵒᵖ, Function.Injective (φ.hom.app U))
    (hker : ∀ (U : Cᵒᵖ) (x : A.obj.obj U), g.hom.app U x = 0 → ∃ y, φ.hom.app U y = x)
    (hcomp : φ ≫ g = 0) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J (fibreSheaf g hT s) where
  exists_finite_cover U := by
    refine ⟨_, _, _, exists_covering_nonempty g hT s U, fun i => ⟨(forget _).obj M,
      inferInstanceAs (Finite M), ?_⟩⟩
    obtain ⟨t₀⟩ := i.2.2
    exact ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIsoType J hT i.1).symm.app _ ≪≫
      (J.overPullback (Type w) i.1).mapIso
        ((constantCommuteCompose J (forget AddCommGrpCat.{w})).symm.app M) ≪≫
      overIso g hT s φ hφ hker hcomp i.1 t₀⟩

end Constant

end Stacks.FibreSheaf

end
