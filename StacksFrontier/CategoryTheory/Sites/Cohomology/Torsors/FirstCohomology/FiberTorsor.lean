module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.AbelianTorsor

/-!
# The fiber torsor of a short exact sequence

For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves and a global
section `q` of `S.X₃`, the fiber of `S.X₂ → S.X₃` over `q` is a torsor under `S.X₁`.  This
file constructs it, shows that a torsor embeds equivariantly in that fiber exactly when it is
isomorphic to it, and collects the facts about global sections as morphisms from the constant
presheaf of integers and about locally surjective morphisms that are used later.

## Main definitions

* `Stacks.Cohomology.Torsors.fiberPresheaf` is the pointwise fiber over a section.
* `Stacks.Cohomology.Torsors.fiberTorsor` is the fiber, as a torsor under the kernel.

## Main results

* `Stacks.Cohomology.Torsors.fiberEmbedding_iff_isomorphic`: a torsor embeds in the fiber
  exactly when it is isomorphic to the fiber torsor.
* `Stacks.Cohomology.Torsors.sheafify_map_epi_of_locallySurjective`: a locally surjective
  morphism of abelian presheaves becomes an epimorphism after sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- A morphism from the constant presheaf of integers is natural on the section `1`. -/
private theorem map_app_one_eq {A : Cᵒᵖ ⥤ AddCommGrpCat.{t}}
    (r : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A) {U V : Cᵒᵖ} (f : U ⟶ V) :
    A.map f (r.app U ⟨1⟩) = r.app V ⟨1⟩ := by
  have h := NatTrans.naturality_apply r f (⟨1⟩ : ULift.{t} ℤ)
  simpa using h.symm

/-- The pointwise fiber of a morphism of abelian sheaves over a section of its
target. -/
public def fiberPresheaf (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    Cᵒᵖ ⥤ Type t where
  obj U := {x : S.X₂.obj.obj U // S.g.hom.app U x = q.app U ⟨1⟩}
  map {U V} f := ↾(fun x => ⟨S.X₂.obj.map f x.1, by
    calc
      S.g.hom.app V (S.X₂.obj.map f x.1) =
          S.X₃.obj.map f (S.g.hom.app U x.1) :=
        NatTrans.naturality_apply S.g.hom f x.1
      _ = S.X₃.obj.map f (q.app U ⟨1⟩) := congrArg _ x.2
      _ = q.app V ⟨1⟩ := by
        have h := NatTrans.naturality_apply q f (⟨1⟩ : ULift.{t} ℤ)
        simpa using h.symm⟩)
  map_id := by
    intro U
    ext x
    simp
  map_comp := by
    intro U V W f g
    ext x
    simp

/-- The fiber presheaf includes into the middle sheaf. -/
public def fiberInclusion (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    fiberPresheaf S q ⟶ S.X₂.obj ⋙ forget AddCommGrpCat where
  app U := ↾Subtype.val
  naturality := by
    intro U V f
    ext x
    rfl

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Fibers of maps of sheaves over global sections satisfy the sheaf condition. -/
public lemma fiberPresheaf_isSheaf
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    Presheaf.IsSheaf J (fiberPresheaf S q) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR x hx
  let E := S.X₂.obj ⋙ forget AddCommGrpCat
  let Q := S.X₃.obj ⋙ forget AddCommGrpCat
  have hE : Presieve.IsSheaf J E :=
    (isSheaf_iff_isSheaf_of_type J E).1
      (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) S.X₂.property)
  have hQ : Presieve.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J Q).1
      (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) S.X₃.property)
  let i := fiberInclusion S q
  obtain ⟨e, he, hue⟩ := (hE R hR) (x.map i) (hx.map i)
  have he' (V : C) (f : V ⟶ U) (hf : R.arrows f) :
      S.X₂.obj.map f.op e = (x f hf).1 := by
    have h := he f hf
    simp only [E, i, fiberInclusion, Presieve.FamilyOfElements.map] at h
    exact h
  have heq : S.g.hom.app (Opposite.op U) e = q.app (Opposite.op U) ⟨1⟩ := by
    apply (hQ R hR).isSeparatedFor.ext
    intro V f hf
    calc
      S.X₃.obj.map f.op (S.g.hom.app (Opposite.op U) e) =
          S.g.hom.app (Opposite.op V) (S.X₂.obj.map f.op e) :=
        (NatTrans.naturality_apply S.g.hom f.op e).symm
      _ = S.g.hom.app (Opposite.op V) (x f hf).1 := by rw [he' V f hf]
      _ = q.app (Opposite.op V) ⟨1⟩ := (x f hf).2
      _ = S.X₃.obj.map f.op (q.app (Opposite.op U) ⟨1⟩) := (map_app_one_eq q f.op).symm
  refine ⟨⟨e, heq⟩, ?_, ?_⟩
  · intro V f hf
    exact Subtype.ext (he' V f hf)
  · intro e' he'
    exact Subtype.ext (hue e'.1 (he'.map i))

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- A short exact sequence of abelian sheaves is left exact on sections. -/
public lemma shortExact_sections_left_exact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact) (U : Cᵒᵖ) :
    Function.Injective (S.f.hom.app U) ∧
      ∀ x : S.X₂.obj.obj U, S.g.hom.app U x = 0 →
        ∃ y : S.X₁.obj.obj U, S.f.hom.app U y = x := by
  let ev : Sheaf J AddCommGrpCat.{t} ⥤ AddCommGrpCat.{t} :=
    sheafToPresheaf J AddCommGrpCat ⋙
      (evaluation Cᵒᵖ AddCommGrpCat).obj U
  have h : (S.map ev).Exact ∧ Mono (ev.map S.f) :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono ev).1
      (inferInstance : Limits.PreservesFiniteLimits ev) S hS
  exact ⟨(AddCommGrpCat.mono_iff_injective _).1 h.2, (ShortComplex.ab_exact_iff (S.map ev)).1 h.1⟩

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The composite of the two maps of a short complex vanishes on sections. -/
public lemma shortComplex_sections_zero
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (U : Cᵒᵖ)
    (a : S.X₁.obj.obj U) :
    S.g.hom.app U (S.f.hom.app U a) = 0 :=
  congrArg (fun k : S.X₁ ⟶ S.X₃ => k.hom.app U a) S.zero

/-- The fiber of a short exact sequence over a section carries the canonical
simply transitive action of its kernel sheaf. -/
public def fiberPseudoTorsor
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    PseudoTorsor (abelianSheafAsGroupSheaf S.X₁) where
  presheaf := fiberPresheaf S q
  isSheaf := fiberPresheaf_isSheaf S q
  act U h x := ⟨S.f.hom.app U (Multiplicative.toAdd h) + x.1, by
    rw [map_add, shortComplex_sections_zero S U, zero_add, x.2]⟩
  one_act := by
    intro U x
    apply Subtype.ext
    change S.f.hom.app U 0 + x.1 = x.1
    simp
  mul_act := by
    intro U g h x
    apply Subtype.ext
    change S.f.hom.app U ((Multiplicative.toAdd g : S.X₁.obj.obj U) +
      (Multiplicative.toAdd h : S.X₁.obj.obj U)) + x.1 =
      S.f.hom.app U (Multiplicative.toAdd g : S.X₁.obj.obj U) +
        (S.f.hom.app U (Multiplicative.toAdd h : S.X₁.obj.obj U) + x.1)
    rw [map_add, add_assoc]
  naturality := by
    intro U V f g x
    apply Subtype.ext
    change S.X₂.obj.map f (S.f.hom.app U (Multiplicative.toAdd g) + x.1) =
      S.f.hom.app V (S.X₁.obj.map f (Multiplicative.toAdd g)) +
        S.X₂.obj.map f x.1
    rw [map_add, NatTrans.naturality_apply]
  simplyTransitive := by
    intro U _ s t
    have hker : S.g.hom.app U (t.1 - s.1) = 0 := by
      rw [map_sub, t.2, s.2, sub_self]
    obtain ⟨a, ha⟩ := (shortExact_sections_left_exact S hS U).2 _ hker
    refine ⟨Multiplicative.ofAdd a, ?_, ?_⟩
    · apply Subtype.ext
      change S.f.hom.app U a + s.1 = t.1
      rw [ha]
      exact sub_add_cancel t.1 s.1
    · intro g hg
      change Multiplicative.toAdd g = a
      have h := congrArg Subtype.val hg
      change S.f.hom.app U (Multiplicative.toAdd g) + s.1 = t.1 at h
      exact (shortExact_sections_left_exact S hS U).1 ((eq_sub_iff_add_eq.mpr h).trans ha.symm)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The canonical inclusion of a fiber is equivariant, injective, and has
exactly the prescribed fiber as its image. -/
public lemma fiberInclusion_spec
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    (∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U)
        (s : (fiberPseudoTorsor S hS q).presheaf.obj U),
      let iU : (fiberPseudoTorsor S hS q).presheaf.obj U → S.X₂.obj.obj U :=
        (fiberInclusion S q).app U
      iU ((fiberPseudoTorsor S hS q).act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s) ∧
    (∀ U : Cᵒᵖ, Function.Injective ((fiberInclusion S q).app U)) ∧
    (∀ (U : Cᵒᵖ) (x : S.X₂.obj.obj U),
      S.g.hom.app U x = q.app U ⟨1⟩ ↔
        ∃ s, (fiberInclusion S q).app U s = x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U h s
    rfl
  · intro U x y h
    exact Subtype.ext h
  · intro U x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.2

/-- Sections of an abelian sheaf that locally lie in the image of a morphism
form a subgroup. -/
public def localImageSubgroup
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (U : Cᵒᵖ) :
    AddSubgroup (S.X₃.obj.obj U) where
  carrier := {y | Presheaf.imageSieve S.g.hom y ∈ J U.unop}
  zero_mem' := by
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U.unop)
    intro V f _
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine J.superset_covering (S := Presheaf.imageSieve S.g.hom x ⊓
      Presheaf.imageSieve S.g.hom y) (fun V f hf => ?_) (J.intersection_covering hx hy)
    obtain ⟨a, ha⟩ := hf.1
    obtain ⟨b, hb⟩ := hf.2
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  neg_mem' := by
    intro x hx
    refine J.superset_covering (S := Presheaf.imageSieve S.g.hom x) (fun V f hf => ?_) hx
    obtain ⟨a, ha⟩ := hf
    exact ⟨-a, by rw [map_neg, map_neg, ha]⟩

/-- The presheaf of sections locally in the image of the second map. -/
public def localImagePresheaf
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    Cᵒᵖ ⥤ AddCommGrpCat.{t} where
  obj U := AddCommGrpCat.of (localImageSubgroup S U)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun y := ⟨S.X₃.obj.map f y.1, by
        change Presheaf.imageSieve S.g.hom (S.X₃.obj.map f y.1) ∈ J V.unop
        simpa [Presheaf.pullback_imageSieve] using
          (J.pullback_stable f.unop y.2)⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp }
  map_id := by
    intro U
    ext x
    simp
  map_comp := by
    intro U V W f g
    ext x
    simp

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The locally generated image is a sheaf of abelian groups. -/
public lemma localImagePresheaf_isSheaf
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    Presheaf.IsSheaf J (localImagePresheaf S) := by
  apply Presheaf.isSheaf_of_isSheaf_comp (J := J) (P := localImagePresheaf S)
    (forget AddCommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  let R : Subfunctor (S.X₃.obj ⋙ forget AddCommGrpCat) :=
    Subfunctor.range (Functor.whiskerRight S.g.hom (forget AddCommGrpCat))
  change Presieve.IsSheaf J ((R.sheafify J).toFunctor)
  exact R.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) S.X₃.property))

/-- The sheaf of sections locally in the image. -/
public def localImageSheaf
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    Sheaf J AddCommGrpCat.{t} where
  obj := localImagePresheaf S
  property := localImagePresheaf_isSheaf S

/-- Inclusion of the locally generated image into the target sheaf. -/
public def localImageInclusion
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    localImageSheaf S ⟶ S.X₃ where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (localImageSubgroup S U).subtype
      naturality := by
        intro U V f
        ext x
        rfl }

/-- The original morphism factors through its locally generated image. -/
public def localImageFactor
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    S.X₂ ⟶ localImageSheaf S where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x => ⟨S.g.hom.app U x, by
            change Presheaf.imageSieve S.g.hom (S.g.hom.app U x) ∈ J U.unop
            rw [Presheaf.imageSieve_app]
            exact J.top_mem U.unop⟩
          map_zero' := by
            apply Subtype.ext
            simp
          map_add' := by
            intro x y
            apply Subtype.ext
            simp }
      naturality := by
        intro U V f
        ext x
        exact Subtype.ext (NatTrans.naturality_apply S.g.hom f x) }

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma localImageFactor_comp_inclusion
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) :
    localImageFactor S ≫ localImageInclusion S = S.g := by
  ext U x
  rfl

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Epimorphisms of abelian sheaves lift sections locally, without a size
restriction on the coefficient groups. -/
public lemma shortExact_locallySurjective
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact) :
    ∀ (U : Cᵒᵖ) (y : S.X₃.obj.obj U),
      Presheaf.imageSieve S.g.hom y ∈ J U.unop := by
  have hmono : Mono (localImageInclusion S) := by
    have hmono' : Mono (localImageInclusion S).hom :=
      (NatTrans.mono_iff_mono_app (localImageInclusion S).hom).2 (by
        intro U
        exact (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective)
    let : Mono (localImageInclusion S).hom := hmono'
    exact Sheaf.Hom.mono_of_presheaf_mono J AddCommGrpCat (localImageInclusion S)
  have hepi : Epi (localImageInclusion S) := by
    let : Epi S.g := hS.epi_g
    exact epi_of_epi_fac (localImageFactor_comp_inclusion S)
  let : Mono (localImageInclusion S) := hmono
  let : Epi (localImageInclusion S) := hepi
  let : IsIso (localImageInclusion S) := isIso_of_mono_of_epi _
  intro U y
  let : IsIso ((localImageInclusion S).hom.app U) := inferInstance
  obtain ⟨z, hz⟩ :=
    (ConcreteCategory.bijective_of_isIso ((localImageInclusion S).hom.app U)).2 y
  change z.1 = y at hz
  have hz' : Presheaf.imageSieve S.g.hom z.1 ∈ J U.unop := z.2
  simpa [hz] using hz'

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Fibers of the quotient map of a short exact sequence are locally
nonempty. -/
public lemma fiberPseudoTorsor_isTorsor
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    (fiberPseudoTorsor S hS q).IsTorsor := by
  intro U
  let y : S.X₃.obj.obj (Opposite.op U) := q.app (Opposite.op U) ⟨1⟩
  refine ⟨Presheaf.imageSieve S.g.hom y,
    shortExact_locallySurjective S hS (Opposite.op U) y, ?_⟩
  rintro V f ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩⟩
  exact hx.trans (map_app_one_eq q f.op)

/-- The torsor associated to a section of the quotient sheaf. -/
public def fiberTorsor
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj) :
    AbelianTorsor S.X₁ :=
  ⟨fiberPseudoTorsor S hS q, fiberPseudoTorsor_isTorsor S hS q⟩

/-- Translation by a global section of the middle sheaf maps a fiber torsor
to the corresponding translated fiber. -/
public def fiberTranslate
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q q' : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (b : ∀ U, S.X₂.obj.obj U)
    (hbNat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), S.X₂.obj.map f (b U) = b V)
    (hb : ∀ U : Cᵒᵖ, q'.app U ⟨1⟩ = q.app U ⟨1⟩ + S.g.hom.app U (b U)) :
    (fiberPseudoTorsor S hS q).Hom (fiberPseudoTorsor S hS q') where
  hom :=
    { app := fun U => ↾(fun x => ⟨x.1 + b U, by
        rw [map_add, x.2]
        exact (hb U).symm⟩)
      naturality := by
        intro U V f
        ext x
        apply Subtype.ext
        change S.X₂.obj.map f x.1 + b V =
          S.X₂.obj.map f (x.1 + b U)
        rw [map_add, hbNat f] }
  map_act := by
    intro U g s
    apply Subtype.ext
    change (S.f.hom.app U (Multiplicative.toAdd g) + s.1) + b U =
      S.f.hom.app U (Multiplicative.toAdd g) + (s.1 + b U)
    abel

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Translation of fibers is an equivariant isomorphism. -/
public lemma fiberTranslate_isIso
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q q' : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (b : ∀ U, S.X₂.obj.obj U)
    (hbNat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), S.X₂.obj.map f (b U) = b V)
    (hb : ∀ U : Cᵒᵖ, q'.app U ⟨1⟩ = q.app U ⟨1⟩ + S.g.hom.app U (b U)) :
    (fiberTranslate S hS q q' b hbNat hb).IsIso := by
  change IsIso (fiberTranslate S hS q q' b hbNat hb).hom
  have hU : ∀ U, IsIso ((fiberTranslate S hS q q' b hbNat hb).hom.app U) := by
    intro U
    rw [isIso_iff_bijective]
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · apply Subtype.ext
      have h' := congrArg Subtype.val h
      change x.1 + b U = y.1 + b U at h'
      exact add_right_cancel h'
    · refine ⟨⟨y.1 - b U, ?_⟩, ?_⟩
      · have hy := y.2
        change S.g.hom.app U y.1 = q'.app U ⟨1⟩ at hy
        rw [map_sub, hy, hb]
        abel
      · apply Subtype.ext
        change (y.1 - b U) + b U = y.1
        abel
  exact NatIso.isIso_of_isIso_app _

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- A sectionwise fiber embedding gives an equivariant isomorphism with the
canonical fiber torsor. -/
public lemma fiberEmbedding_iff_isomorphic
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁) :
    (∃ i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat,
      (∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
        let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
        iU (F.1.act U (Multiplicative.ofAdd h) s) = S.f.hom.app U h + iU s) ∧
      (∀ U : Cᵒᵖ, Function.Injective (i.app U)) ∧
      (∀ (U : Cᵒᵖ) (x : S.X₂.obj.obj U),
        S.g.hom.app U x = q.app U ⟨1⟩ ↔ ∃ s, i.app U s = x)) ↔
      F.IsIsomorphic (fiberTorsor S hS q) := by
  constructor
  · rintro ⟨i, hiAct, hiInj, hiRange⟩
    let e : F.1.Hom (fiberPseudoTorsor S hS q) :=
      { hom :=
          { app := fun U => ↾(fun s =>
              ⟨i.app U s, (hiRange U (i.app U s)).2 ⟨s, rfl⟩⟩)
            naturality := by
              intro U V f
              ext s
              apply Subtype.ext
              exact NatTrans.naturality_apply i f s }
        map_act := fun U g s => Subtype.ext (hiAct U (Multiplicative.toAdd g) s) }
    refine ⟨e, ?_⟩
    change IsIso e.hom
    have hApp : ∀ U, IsIso (e.hom.app U) := by
      intro U
      rw [isIso_iff_bijective]
      refine ⟨fun s s' hs => hiInj U (congrArg Subtype.val hs), fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hiRange U x.1).1 x.2
      exact ⟨s, Subtype.ext hs⟩
    exact NatIso.isIso_of_isIso_app _
  · rintro ⟨e, he⟩
    let : IsIso e.hom := he
    let i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat :=
      e.hom ≫ fiberInclusion S q
    refine ⟨i, ?_, ?_, ?_⟩
    · intro U h s
      exact congrArg Subtype.val (e.map_act U (Multiplicative.ofAdd h) s)
    · intro U s s' hs
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1 (Subtype.ext hs)
    · intro U x
      constructor
      · intro hx
        obtain ⟨s, hs⟩ :=
          (ConcreteCategory.bijective_of_isIso (e.hom.app U)).2 (⟨x, hx⟩ :
            (fiberPseudoTorsor S hS q).presheaf.obj U)
        exact ⟨s, congrArg Subtype.val hs⟩
      · rintro ⟨s, rfl⟩
        exact (e.hom.app U s).2

/-- The homomorphism out of the integers determined by an element sends `1` to it. -/
private theorem uliftZMultiplesHom_apply_one {G : AddCommGrpCat.{t}} (g : G) :
    ((uliftZMultiplesHom G) g) ⟨1⟩ = g := by
  rw [uliftZMultiplesHom_apply_apply]
  change (1 : ℤ) • g = g
  simp

/-- A compatible family of sections of an abelian presheaf is equivalently a
morphism from the constant presheaf of integers. -/
public def morphismOfSectionFamily (A : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (s : ∀ U, A.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), A.map f (s U) = s V) :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A where
  app U := AddCommGrpCat.ofHom ((uliftZMultiplesHom _) (s U))
  naturality := by
    intro U V f
    ext n
    change ((uliftZMultiplesHom _) (s V)) n =
      A.map f (((uliftZMultiplesHom _) (s U)) n)
    simp only [uliftZMultiplesHom_apply_apply, map_zsmul, hs]

public lemma morphismOfSectionFamily_one (A : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (s : ∀ U, A.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), A.map f (s U) = s V)
    (U : Cᵒᵖ) :
    (morphismOfSectionFamily A s hs).app U ⟨1⟩ = s U := by
  exact uliftZMultiplesHom_apply_one (s U)

public lemma sectionFamilyOfMorphism_naturality
    (A : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (r : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    A.map f (r.app U ⟨1⟩) = r.app V ⟨1⟩ := by
  exact map_app_one_eq r f

public lemma liftedInt_hom_ext {G : AddCommGrpCat.{t}}
    (f g : AddCommGrpCat.of (ULift.{t} ℤ) ⟶ G)
    (h : f ⟨1⟩ = g ⟨1⟩) : f = g :=
  AddCommGrpCat.hom_ext ((uliftZMultiplesHom G).symm.injective h)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Morphisms from a locally covered abelian presheaf into a sheaf are
determined by their restriction to the covering presheaf. -/
public lemma locallySurjective_hom_ext
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{t}} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f]
    (Y : Sheaf J AddCommGrpCat.{t}) (a b : Q ⟶ Y.obj)
    (h : f ≫ a = f ≫ b) : a = b := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext x
  let e₁ : AddCommGrpCat.of (ULift.{t} ℤ) ⟶ Y.obj.obj U :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom _) (a.app U x))
  let e₂ : AddCommGrpCat.of (ULift.{t} ℤ) ⟶ Y.obj.obj U :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom _) (b.app U x))
  have he : e₁ = e₂ := by
    refine Y.property.hom_ext
      ⟨Presheaf.imageSieve f x, Presheaf.imageSieve_mem J f x⟩ e₁ e₂ ?_
    intro I
    apply liftedInt_hom_ext
    let y := Presheaf.localPreimage f x I.f I.hf
    have hxy : f.app (Opposite.op I.Y) y = Q.map I.f.op x :=
      Presheaf.app_localPreimage f x I.f I.hf
    have hfa : a.app (Opposite.op I.Y) (f.app (Opposite.op I.Y) y) =
        b.app (Opposite.op I.Y) (f.app (Opposite.op I.Y) y) :=
      congrArg (fun α => α.app (Opposite.op I.Y) y) h
    rw [hxy] at hfa
    have ha := NatTrans.naturality_apply a I.f.op x
    have hb := NatTrans.naturality_apply b I.f.op x
    change Y.obj.map I.f.op (e₁ ⟨1⟩) = Y.obj.map I.f.op (e₂ ⟨1⟩)
    rw [show e₁ ⟨1⟩ = a.app U x from uliftZMultiplesHom_apply_one _,
      show e₂ ⟨1⟩ = b.app U x from uliftZMultiplesHom_apply_one _]
    exact ha.symm.trans (hfa.trans hb)
  have h₁ := congrArg (fun z : AddCommGrpCat.of (ULift.{t} ℤ) ⟶ Y.obj.obj U =>
    z ⟨1⟩) he
  change ((uliftZMultiplesHom _) (a.app U x)) ⟨1⟩ =
    ((uliftZMultiplesHom _) (b.app U x)) ⟨1⟩ at h₁
  rwa [uliftZMultiplesHom_apply_one, uliftZMultiplesHom_apply_one] at h₁

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- A locally surjective morphism of abelian presheaves becomes an epimorphism
after sheafification. -/
public lemma sheafify_map_epi_of_locallySurjective
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{t}} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Epi ((presheafToSheaf J AddCommGrpCat).map f) := by
  constructor
  intro Y a b h
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  apply (adj.homEquiv Q Y).injective
  apply locallySurjective_hom_ext f Y _ _
  exact (adj.homEquiv_naturality_left f a).symm.trans
    ((congrArg (adj.homEquiv P Y) h).trans (adj.homEquiv_naturality_left f b))

end Stacks.Cohomology.Torsors
