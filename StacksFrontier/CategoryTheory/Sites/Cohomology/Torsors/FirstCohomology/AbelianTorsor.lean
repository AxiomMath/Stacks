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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsors under an abelian sheaf and their differences

For an abelian sheaf `H` on a site, this file sets up torsors under `H` and their
isomorphism classes, the difference of two sections of a torsor, and the free abelian
presheaf on a torsor together with the affine-linear maps out of it.

## Main definitions

* `Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf` regards an abelian sheaf as a
  multiplicatively written sheaf of groups.
* `Stacks.Cohomology.Torsors.AbelianTorsor` is the type of torsors under an abelian sheaf.
* `Stacks.Cohomology.Torsors.torsorSetoid` is equivariant isomorphism as a setoid.
* `Stacks.Cohomology.Torsors.torsorIsoClasses` is its quotient.
* `Stacks.Cohomology.Torsors.torsorDifference` is the difference of two sections of a torsor.
* `Stacks.Cohomology.Torsors.torsorSheafAugmentationKernelMap` is the map from the
  augmentation kernel of the free abelian sheaf on a torsor to the abelian sheaf.

## Implementation notes

The torsor interface uses multiplicative groups, so an abelian sheaf is first
transported along the standard equivalence from additive commutative groups to
multiplicative commutative groups.  Two torsors represent the same class
precisely when an equivariant torsor morphism between them has an isomorphism
as its underlying natural transformation.
The universe of sections is independent of the universes of the site.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v u

namespace Stacks.Cohomology.Torsors

/-- An extension class is the boundary of a morphism to the quotient of an
injective object. -/
public lemma ext_one_boundary_surjective
    {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{w} D]
    (S : ShortComplex D) (hS : S.ShortExact) [Injective S.X₂]
    (X : D) (x : Abelian.Ext X S.X₁ 1) :
    ∃ q : X ⟶ S.X₃,
      (Abelian.Ext.mk₀ q).comp hS.extClass (zero_add 1) = x := by
  obtain ⟨y, hy⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ X hS x
      (by exact Abelian.Ext.eq_zero_of_injective _) (zero_add 1)
  exact ⟨Abelian.Ext.homEquiv₀ y, by simpa only [Abelian.Ext.mk₀_homEquiv₀_apply] using hy⟩

/-- A morphism to the quotient has zero boundary precisely when it lifts to the
middle object of the short exact sequence. -/
public lemma ext_one_boundary_eq_zero_iff_lift
    {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{w} D]
    (S : ShortComplex D) (hS : S.ShortExact) (X : D) (q : X ⟶ S.X₃) :
    (Abelian.Ext.mk₀ q).comp hS.extClass (zero_add 1) = 0 ↔
      ∃ f : X ⟶ S.X₂, f ≫ S.g = q := by
  constructor
  · intro hq
    obtain ⟨y, hy⟩ :=
      Abelian.Ext.covariant_sequence_exact₃ X hS (Abelian.Ext.mk₀ q)
        (zero_add 1) hq
    refine ⟨Abelian.Ext.homEquiv₀ y, ?_⟩
    apply (Abelian.Ext.mk₀_bijective _ _).1
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hy
  · rintro ⟨f, rfl⟩
    rw [← Abelian.Ext.mk₀_comp_mk₀_assoc]
    simp only [hS.comp_extClass, Abelian.Ext.comp_zero]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An abelian sheaf, regarded as a sheaf of multiplicatively written groups. -/
public noncomputable def abelianSheafAsGroupSheaf
    (H : Sheaf J AddCommGrpCat.{t}) : SheafOfGroups (C := C) J := by
  letI : AddCommGrpCat.toCommGrp.{t}.IsEquivalence :=
    commGroupAddCommGroupEquivalence.{t}.isEquivalence_inverse
  exact
    { presheaf := H.obj ⋙ AddCommGrpCat.toCommGrp.{t} ⋙ forget CommGrpCat.{t}
      isSheaf := Presheaf.isSheaf_comp_of_isSheaf J _ (forget CommGrpCat.{t})
        (Presheaf.isSheaf_comp_of_isSheaf J _ AddCommGrpCat.toCommGrp.{t} H.property)
      group := fun U => inferInstanceAs (Group (Multiplicative (H.obj.obj U)))
      map_mul := by
        intro U V f
        let : Group ((H.obj ⋙ AddCommGrpCat.toCommGrp ⋙
            forget CommGrpCat.{t}).obj U) :=
          inferInstanceAs (Group (Multiplicative (H.obj.obj U)))
        let : Group ((H.obj ⋙ AddCommGrpCat.toCommGrp ⋙
            forget CommGrpCat.{t}).obj V) :=
          inferInstanceAs (Group (Multiplicative (H.obj.obj V)))
        intro g h
        change Multiplicative.ofAdd
          (H.obj.map f ((Multiplicative.toAdd g : H.obj.obj U) +
            (Multiplicative.toAdd h : H.obj.obj U))) =
            Multiplicative.ofAdd (H.obj.map f (Multiplicative.toAdd g : H.obj.obj U)) *
              Multiplicative.ofAdd (H.obj.map f (Multiplicative.toAdd h : H.obj.obj U))
        rw [map_add]
        rfl }

/-- A torsor under the multiplicative group sheaf underlying an abelian sheaf. -/
@[sga "4½ Arcata 1.6.6"]
public abbrev AbelianTorsor (H : Sheaf J AddCommGrpCat.{t}) :=
  {F : PseudoTorsor.{t} (abelianSheafAsGroupSheaf H) // F.IsTorsor}

/-- Two torsors under an abelian sheaf are isomorphic when there is an
equivariant morphism between them whose underlying presheaf morphism is an
isomorphism. -/
public def AbelianTorsor.IsIsomorphic {H : Sheaf J AddCommGrpCat.{t}}
    (F F' : AbelianTorsor H) : Prop :=
  ∃ e : F.1.Hom F'.1, e.IsIso

/-- Equivariant isomorphism is an equivalence relation on torsors under an
abelian sheaf. -/
public def torsorSetoid (H : Sheaf J AddCommGrpCat.{t}) : Setoid (AbelianTorsor H) where
  r := AbelianTorsor.IsIsomorphic
  iseqv := {
    refl := by
      intro F
      let e : F.1.Hom F.1 := { hom := 𝟙 _, map_act := by simp }
      refine ⟨e, ?_⟩
      change IsIso e.hom
      infer_instance
    symm := by
      intro F F' h
      obtain ⟨e, he⟩ := h
      let : IsIso e.hom := he
      let eInv : PseudoTorsor.Hom F'.1 F.1 :=
        { hom := inv e.hom
          map_act := by
            intro U g s
            apply (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
            rw [e.map_act]
            simp }
      refine ⟨eInv, ?_⟩
      change IsIso eInv.hom
      dsimp [eInv]
      infer_instance
    trans := by
      intro F F' F'' h h'
      obtain ⟨e, he⟩ := h
      obtain ⟨e', he'⟩ := h'
      let : IsIso e.hom := he
      let : IsIso e'.hom := he'
      let ee' : PseudoTorsor.Hom F.1 F''.1 :=
        { hom := e.hom ≫ e'.hom
          map_act := by
            intro U g s
            simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
            rw [e.map_act, e'.map_act] }
      refine ⟨ee', ?_⟩
      change IsIso ee'.hom
      dsimp [ee']
      infer_instance }

/-- The type of isomorphism classes of torsors under an abelian sheaf. -/
@[sga "4½ Arcata 1.6.6"]
public def torsorIsoClasses (H : Sheaf J AddCommGrpCat.{t}) :
    Type (max u v (t + 1)) :=
  Quotient (torsorSetoid H)

/-- The action map of a pseudo-torsor at a single section is bijective. -/
private theorem act_bijective_at {G : SheafOfGroups (C := C) J} (F : PseudoTorsor G)
    (U : Cᵒᵖ) (s : F.presheaf.obj U) : Function.Bijective (fun g => F.act U g s) := by
  refine ⟨fun g₁ g₂ h => ?_, fun x => ?_⟩
  · obtain ⟨g, _, uniq⟩ := F.simplyTransitive U ⟨s⟩ s (F.act U g₁ s)
    rw [uniq g₁ rfl, uniq g₂ h.symm]
  · obtain ⟨g, hg, _⟩ := F.simplyTransitive U ⟨s⟩ s x
    exact ⟨g, hg⟩

/-- Two additive maps out of a free abelian group agree on `map g x` and `x` if they agree on
generators. -/
private theorem lift_map_apply_eq {X Y M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (L : FreeAbelianGroup Y →+ N) (g : X → Y) (T : FreeAbelianGroup X →+ M) (k : M →+ N)
    (h : ∀ s, L (FreeAbelianGroup.of (g s)) = k (T (FreeAbelianGroup.of s)))
    (x : FreeAbelianGroup X) : L (FreeAbelianGroup.map g x) = k (T x) :=
  DFunLike.congr_fun (FreeAbelianGroup.lift_ext (L.comp (FreeAbelianGroup.map g)) (k.comp T)
    fun s => by simpa only [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply] using h s) x

variable [HasSheafify J AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The action map of a torsor at a chosen section is bijective.  This is the
sectionwise bridge between the torsor interface and the concrete presheaf
maps used below. -/
public lemma action_bijective (H : Sheaf J AddCommGrpCat.{t})
    (F : PseudoTorsor (C := C)
    (abelianSheafAsGroupSheaf (J := J) (C := C) H))
    (_hF : F.IsTorsor) (s : ∀ U, F.presheaf.obj U) (U : Cᵒᵖ) :
    Function.Bijective (fun g => F.act U g (s U)) := by
  exact act_bijective_at F U (s U)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- An equivariant map of pseudo-torsors is an isomorphism when its source has
a section over every object. -/
public lemma torsorHom_isIso_of_sections (H : Sheaf J AddCommGrpCat.{t})
    {F F' : PseudoTorsor (C := C) (abelianSheafAsGroupSheaf (J := J) H)}
    (e : F.Hom F') (hne : ∀ U, Nonempty (F.presheaf.obj U)) :
    e.IsIso := by
  change IsIso e.hom
  have hcomp : ∀ U, IsIso (e.hom.app U) := by
    intro U
    rw [isIso_iff_bijective]
    obtain ⟨s⟩ := hne U
    have hs := act_bijective_at F U s
    have hs' := act_bijective_at F' U (e.hom.app U s)
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · obtain ⟨gx, rfl⟩ := hs.2 x
      obtain ⟨gy, rfl⟩ := hs.2 y
      exact congrArg (fun g => F.act U g s) (hs'.1 (by simpa only [e.map_act] using hxy))
    · obtain ⟨g, rfl⟩ := hs'.2 y
      exact ⟨F.act U g s, e.map_act U g s⟩
  exact NatIso.isIso_of_isIso_app _

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- An equivariant map between torsors is injective on every set of sections. -/
public lemma torsorHom_injective (H : Sheaf J AddCommGrpCat.{t})
    (F F' : AbelianTorsor H) (e : F.1.Hom F'.1) (U : Cᵒᵖ) :
    Function.Injective (e.hom.app U) := by
  intro s s' h
  obtain ⟨g, hg, _⟩ := F.1.simplyTransitive U ⟨s⟩ s s'
  have hge : F'.1.act U g (e.hom.app U s) = e.hom.app U s := by
    calc
      F'.1.act U g (e.hom.app U s) = e.hom.app U (F.1.act U g s) :=
        (e.map_act U g s).symm
      _ = e.hom.app U s' := congrArg (e.hom.app U) hg
      _ = e.hom.app U s := h.symm
  obtain ⟨g₀, _, hu⟩ :=
    F'.1.simplyTransitive U ⟨e.hom.app U s⟩ (e.hom.app U s) (e.hom.app U s)
  calc
    s = F.1.act U 1 s := (F.1.one_act U s).symm
    _ = F.1.act U g s := by rw [(hu g hge).trans (hu 1 (F'.1.one_act U _)).symm]
    _ = s' := hg

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- An equivariant map between torsors is locally surjective. -/
public lemma torsorHom_locallySurjective (H : Sheaf J AddCommGrpCat.{t})
    (F F' : AbelianTorsor H) (e : F.1.Hom F'.1) :
    Presheaf.IsLocallySurjective J e.hom := by
  constructor
  intro U y
  obtain ⟨R, hR, hsections⟩ := F.2 U
  refine J.superset_covering (S := R) (fun V f hf => ?_) hR
  obtain ⟨s⟩ := hsections hf
  let z := F'.1.presheaf.map f.op y
  obtain ⟨g, hg, _⟩ := F'.1.simplyTransitive (Opposite.op V)
    ⟨e.hom.app (Opposite.op V) s⟩ (e.hom.app (Opposite.op V) s) z
  exact ⟨F.1.act (Opposite.op V) g s, by rw [e.map_act, hg]⟩

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Every equivariant map between torsors for the same group sheaf is an
isomorphism. -/
public lemma torsorHom_isIso (H : Sheaf J AddCommGrpCat.{t})
    (F F' : AbelianTorsor H) (e : F.1.Hom F'.1) : e.IsIso := by
  let A : Sheaf J (Type t) := ⟨F.1.presheaf, F.1.isSheaf⟩
  let B : Sheaf J (Type t) := ⟨F'.1.presheaf, F'.1.isSheaf⟩
  let e' : A ⟶ B := ⟨e.hom⟩
  have hInj : Sheaf.IsLocallyInjective e' :=
    Presheaf.isLocallyInjective_of_injective J e.hom
      (torsorHom_injective H F F' e)
  have hSurj : Sheaf.IsLocallySurjective e' :=
    torsorHom_locallySurjective H F F' e
  let : IsIso e' := (Sheaf.isLocallyBijective_iff_isIso e').1 ⟨hInj, hSurj⟩
  change IsIso ((sheafToPresheaf J (Type t)).map e')
  infer_instance

/-- The unique coefficient taking one torsor section to another. -/
public noncomputable def torsorDifference (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s s' : F.1.presheaf.obj U) : H.obj.obj U :=
  Multiplicative.toAdd
    (Classical.choose (F.1.simplyTransitive U ⟨s'⟩ s' s))

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_act (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s s' : F.1.presheaf.obj U) :
    F.1.act U (Multiplicative.ofAdd (torsorDifference H F U s s')) s' = s :=
  (Classical.choose_spec (F.1.simplyTransitive U ⟨s'⟩ s' s)).1

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_eq_of_act (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s s' : F.1.presheaf.obj U) (a : H.obj.obj U)
    (ha : F.1.act U (Multiplicative.ofAdd a) s' = s) :
    torsorDifference H F U s s' = a := by
  have h := (Classical.choose_spec (F.1.simplyTransitive U ⟨s'⟩ s' s)).2
    (Multiplicative.ofAdd a) ha
  exact (congrArg Multiplicative.toAdd h).symm

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The action of a sum of sections, written through `Multiplicative`.  The multiplication on
the group sheaf underlying an abelian sheaf is the addition of that sheaf, but the
identification sits behind a structure projection; it is recorded here once and used instead
of rewriting with `PseudoTorsor.mul_act`. -/
public lemma act_ofAdd_add (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ) (a b : H.obj.obj U)
    (s : F.1.presheaf.obj U) :
    F.1.act U (Multiplicative.ofAdd (a + b)) s =
      F.1.act U (Multiplicative.ofAdd a) (F.1.act U (Multiplicative.ofAdd b) s) :=
  F.1.mul_act U (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) s

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_trans (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s s' s'' : F.1.presheaf.obj U) :
    torsorDifference H F U s s'' =
      torsorDifference H F U s s' + torsorDifference H F U s' s'' := by
  refine torsorDifference_eq_of_act H F U s s'' _ ?_
  refine (act_ofAdd_add H F U _ _ s'').trans ?_
  exact (congrArg (F.1.act U (Multiplicative.ofAdd (torsorDifference H F U s s')))
    (torsorDifference_act H F U s' s'')).trans
    (torsorDifference_act H F U s s')

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_naturality (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) {U V : Cᵒᵖ} (f : U ⟶ V)
    (s s' : F.1.presheaf.obj U) :
    H.obj.map f (torsorDifference H F U s s') =
      torsorDifference H F V (F.1.presheaf.map f s) (F.1.presheaf.map f s') := by
  symm
  apply torsorDifference_eq_of_act
  change F.1.act V
    ((abelianSheafAsGroupSheaf H).presheaf.map f
      (Multiplicative.ofAdd (torsorDifference H F U s s')))
      (F.1.presheaf.map f s') = F.1.presheaf.map f s
  exact (F.1.naturality f _ s').symm.trans
    (congrArg (fun x => F.1.presheaf.map f x) (torsorDifference_act H F U s s'))

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_act_left (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (h : H.obj.obj U) (s s' : F.1.presheaf.obj U) :
    torsorDifference H F U (F.1.act U (Multiplicative.ofAdd h) s) s' =
      h + torsorDifference H F U s s' := by
  rw [torsorDifference_trans H F U _ s s']
  rw [torsorDifference_eq_of_act H F U _ s h rfl]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_self (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ) (s : F.1.presheaf.obj U) :
    torsorDifference H F U s s = 0 :=
  torsorDifference_eq_of_act H F U s s 0 (F.1.one_act U s)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_rev (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s s' : F.1.presheaf.obj U) :
    torsorDifference H F U s s' = -torsorDifference H F U s' s := by
  have h := torsorDifference_trans H F U s s' s
  rw [torsorDifference_self] at h
  exact eq_neg_of_add_eq_zero_left h.symm

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorDifference_act_right (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (h : H.obj.obj U) (s s' : F.1.presheaf.obj U) :
    torsorDifference H F U s (F.1.act U (Multiplicative.ofAdd h) s') =
      torsorDifference H F U s s' - h := by
  rw [torsorDifference_trans H F U s s' _]
  rw [torsorDifference_rev H F U s' _]
  rw [torsorDifference_eq_of_act H F U _ s' h rfl]
  abel

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- An equivariant map carries the difference between sections through the
coefficient morphism. -/
public lemma torsorDifference_map
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s))
    (U : Cᵒᵖ) (s s' : F.1.presheaf.obj U) :
    torsorDifference H' F' U (f.app U s) (f.app U s') =
      φ.hom.app U (torsorDifference H F U s s') := by
  apply torsorDifference_eq_of_act
  rw [← hf, torsorDifference_act]

/-- The free abelian presheaf on a presheaf of sets. -/
public abbrev freeAbelianPresheaf (P : Cᵒᵖ ⥤ Type t) :
    Cᵒᵖ ⥤ AddCommGrpCat.{t} :=
  P ⋙ AddCommGrpCat.free

/-- The augmentation sends every torsor generator to one. -/
public noncomputable def freeAbelianPresheafAugmentation
    (P : Cᵒᵖ ⥤ Type t) :
    freeAbelianPresheaf P ⟶
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) where
  app U := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun _ : P.obj U => (⟨1⟩ : ULift.{t} ℤ)))
  naturality := by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    simp [freeAbelianPresheaf, AddCommGrpCat.free, FreeAbelianGroup.lift_apply_of]

/-- Given a base section of a torsor, linearly extend the difference from
that base section to the free abelian group. -/
public noncomputable def torsorAffineLinearMap (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ) (s₀ : F.1.presheaf.obj U) :
    FreeAbelianGroup (F.1.presheaf.obj U) →+ H.obj.obj U :=
  FreeAbelianGroup.lift (fun s => torsorDifference H F U s s₀)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorAffineLinearMap_of (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ) (s₀ s : F.1.presheaf.obj U) :
    torsorAffineLinearMap H F U s₀ (FreeAbelianGroup.of s) =
    torsorDifference H F U s s₀ :=
  FreeAbelianGroup.lift_apply_of _ _

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Changing the chosen base section alters the affine linear map by the
augmentation times a fixed coefficient. -/
public lemma torsorAffineLinearMap_change_base (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s₀ s₁ : F.1.presheaf.obj U) :
    torsorAffineLinearMap H F U s₁ =
      torsorAffineLinearMap H F U s₀ +
        ((uliftZMultiplesHom _) (torsorDifference H F U s₀ s₁)).comp
          (FreeAbelianGroup.lift
            (fun _ : F.1.presheaf.obj U => (⟨1⟩ : ULift.{t} ℤ))) := by
  apply FreeAbelianGroup.lift_ext
  intro s
  simp only [torsorAffineLinearMap_of, AddMonoidHom.add_apply,
    AddMonoidHom.comp_apply, uliftZMultiplesHom_apply_apply]
  change torsorDifference H F U s s₁ =
    torsorDifference H F U s s₀ + (1 : ℤ) • torsorDifference H F U s₀ s₁
  simpa using torsorDifference_trans H F U s s₀ s₁

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The affine linear map is independent of the chosen basepoint on the
augmentation kernel. -/
public lemma torsorAffineLinearMap_eq_on_augKernel (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s₀ s₁ : F.1.presheaf.obj U)
    (x : FreeAbelianGroup (F.1.presheaf.obj U))
    (hx : (FreeAbelianGroup.lift
      (fun _ : F.1.presheaf.obj U => (⟨1⟩ : ULift.{t} ℤ))) x = 0) :
    torsorAffineLinearMap H F U s₁ x = torsorAffineLinearMap H F U s₀ x := by
  have h := congrArg (fun φ : FreeAbelianGroup (F.1.presheaf.obj U) →+
    H.obj.obj U => φ x) (torsorAffineLinearMap_change_base H F U s₀ s₁)
  simpa [hx] using h

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The affine linear map commutes with restriction when its base section is
also restricted. -/
public lemma torsorAffineLinearMap_naturality (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) {U V : Cᵒᵖ} (f : U ⟶ V)
    (s₀ : F.1.presheaf.obj U) (x : FreeAbelianGroup (F.1.presheaf.obj U)) :
    torsorAffineLinearMap H F V (F.1.presheaf.map f s₀)
        (FreeAbelianGroup.map (F.1.presheaf.map f) x) =
      H.obj.map f (torsorAffineLinearMap H F U s₀ x) := by
  refine lift_map_apply_eq (torsorAffineLinearMap H F V (F.1.presheaf.map f s₀))
    (F.1.presheaf.map f) (torsorAffineLinearMap H F U s₀) (H.obj.map f).hom (fun s => ?_) x
  simpa only [torsorAffineLinearMap_of] using (torsorDifference_naturality H F f s s₀).symm

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The affine map is natural in equivariant morphisms and the coefficient
sheaf. -/
public lemma torsorAffineLinearMap_map
    {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ⟶ H')
    (F : AbelianTorsor H) (F' : AbelianTorsor H')
    (f : F.1.presheaf ⟶ F'.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd h) s) =
        F'.1.act U (Multiplicative.ofAdd (φ.hom.app U h)) (f.app U s))
    (U : Cᵒᵖ) (s₀ : F.1.presheaf.obj U)
    (x : FreeAbelianGroup (F.1.presheaf.obj U)) :
    torsorAffineLinearMap H' F' U (f.app U s₀)
        (FreeAbelianGroup.map (f.app U) x) =
      φ.hom.app U (torsorAffineLinearMap H F U s₀ x) := by
  refine lift_map_apply_eq (torsorAffineLinearMap H' F' U (f.app U s₀)) (f.app U)
    (torsorAffineLinearMap H F U s₀) (φ.hom.app U).hom (fun s => ?_) x
  simpa only [torsorAffineLinearMap_of] using torsorDifference_map φ F F' f hf U s s₀

/-- The augmentation kernel of the free abelian presheaf on a torsor. -/
public abbrev freeAbelianPresheafAugmentationKernel
    (P : Cᵒᵖ ⥤ Type t) : Cᵒᵖ ⥤ AddCommGrpCat.{t} :=
  Limits.kernel (freeAbelianPresheafAugmentation P)

/-- Evaluation of an augmentation-zero formal sum in the coefficient sheaf.
Its value is independent of the base section whenever one exists. -/
public noncomputable def torsorAugmentationKernelMapAt
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) (U : Cᵒᵖ) :
    (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U →+
      H.obj.obj U := by
  classical
  exact if h : Nonempty (F.1.presheaf.obj U) then
    (torsorAffineLinearMap H F U (Classical.choice h)).comp
      ((Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U).hom
  else 0

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Evaluation on the augmentation kernel can use any local torsor section
as its base. -/
public lemma torsorAugmentationKernelMapAt_eq
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) (U : Cᵒᵖ)
    (s₀ : F.1.presheaf.obj U)
    (x : (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U) :
    torsorAugmentationKernelMapAt H F U x =
      torsorAffineLinearMap H F U s₀
        (((Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U) x) := by
  classical
  have hz :
      ((freeAbelianPresheafAugmentation F.1.presheaf).app U)
        (((Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U) x) =
      0 := by
    have h := Limits.kernel.condition (freeAbelianPresheafAugmentation F.1.presheaf)
    have hU := congrArg (fun α => α.app U) h
    have hx := congrArg (fun β => β x) hU
    change ((Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U ≫
      (freeAbelianPresheafAugmentation F.1.presheaf).app U) x = 0 at hx
    simpa only [ConcreteCategory.comp_apply] using hx
  simp only [torsorAugmentationKernelMapAt, dite_eq_left (show Nonempty
    (F.1.presheaf.obj U) from ⟨s₀⟩)]
  exact torsorAffineLinearMap_eq_on_augKernel H F U s₀
    (Classical.choice (show Nonempty (F.1.presheaf.obj U) from ⟨s₀⟩)) _ hz

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorAugmentationKernelMapAt_eq_zero_of_empty
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) (U : Cᵒᵖ)
    (h : ¬ Nonempty (F.1.presheaf.obj U)) :
    torsorAugmentationKernelMapAt H F U = 0 := by
  classical
  simp [torsorAugmentationKernelMapAt, h]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The augmentation-kernel evaluation commutes with restriction. -/
public lemma torsorAugmentationKernelMapAt_naturality
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H)
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U) :
    torsorAugmentationKernelMapAt H F V
      ((freeAbelianPresheafAugmentationKernel F.1.presheaf).map f x) =
    H.obj.map f (torsorAugmentationKernelMapAt H F U x) := by
  classical
  let ι := Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)
  have hnat := NatTrans.naturality_apply ι f x
  by_cases hs : Nonempty (F.1.presheaf.obj U)
  · let s := Classical.choice hs
    rw [torsorAugmentationKernelMapAt_eq H F V (F.1.presheaf.map f s),
      torsorAugmentationKernelMapAt_eq H F U s]
    change torsorAffineLinearMap H F V (F.1.presheaf.map f s)
        (ι.app V ((freeAbelianPresheafAugmentationKernel F.1.presheaf).map f x)) =
      H.obj.map f (torsorAffineLinearMap H F U s (ι.app U x))
    rw [hnat]
    exact torsorAffineLinearMap_naturality H F f s (ι.app U x)
  · have : IsEmpty (F.1.presheaf.obj U) := ⟨fun s => hs ⟨s⟩⟩
    have : Subsingleton ((freeAbelianPresheaf F.1.presheaf).obj U) := by
      change Subsingleton (FreeAbelianGroup (F.1.presheaf.obj U))
      infer_instance
    have hιZero : (ι.app U x : FreeAbelianGroup (F.1.presheaf.obj U)) = 0 :=
      Subsingleton.elim _ _
    have hKZero :
        (freeAbelianPresheafAugmentationKernel F.1.presheaf).map f x = 0 := by
      apply (AddCommGrpCat.mono_iff_injective (ι.app V)).1 inferInstance
      simpa only [hιZero, map_zero] using hnat
    rw [hKZero, map_zero,
      torsorAugmentationKernelMapAt_eq_zero_of_empty H F U hs]
    simp

/-- The canonical difference map on the augmentation kernel, before
sheafification. -/
public noncomputable def torsorAugmentationKernelMap
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    freeAbelianPresheafAugmentationKernel F.1.presheaf ⟶ H.obj where
  app U := AddCommGrpCat.ofHom (torsorAugmentationKernelMapAt H F U)
  naturality := by
    intro U V f
    ext x
    exact torsorAugmentationKernelMapAt_naturality H F f x

/-- The difference map descends from the free abelian presheaf's augmentation
kernel to its sheafification. -/
public noncomputable def torsorSheafAugmentationKernelMap
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    (presheafToSheaf J AddCommGrpCat).obj
      (freeAbelianPresheafAugmentationKernel F.1.presheaf) ⟶ H :=
  ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm
    (torsorAugmentationKernelMap H F)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The sheafified difference map agrees with the original difference map
on presheaf sections. -/
public lemma torsorSheafAugmentationKernelMap_on_sections
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf) ≫
      (torsorSheafAugmentationKernelMap H F).hom =
        torsorAugmentationKernelMap H F := by
  change toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf) ≫
    sheafifyLift J (torsorAugmentationKernelMap H F) H.property = _
  exact toSheafify_sheafifyLift _ _ _

/-- The free abelian sheaf on a presheaf of sets. -/
public noncomputable abbrev freeAbelianSheafOnPresheaf (P : Cᵒᵖ ⥤ Type t) :
    Sheaf J AddCommGrpCat.{t} :=
  (presheafToSheaf J AddCommGrpCat).obj (freeAbelianPresheaf P)

public noncomputable abbrev freeAbelianSheafAugmentation (P : Cᵒᵖ ⥤ Type t) :
    freeAbelianSheafOnPresheaf P ⟶
      (presheafToSheaf J AddCommGrpCat).obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) :=
  (presheafToSheaf J AddCommGrpCat).map (freeAbelianPresheafAugmentation P)

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The augmentation of the free abelian presheaf of a torsor is locally
surjective. -/
public lemma freeAbelianPresheafAugmentation_locallySurjective
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    Presheaf.IsLocallySurjective J
      (freeAbelianPresheafAugmentation F.1.presheaf) := by
  constructor
  intro U y
  obtain ⟨R, hR, hsections⟩ := F.2 U
  refine J.superset_covering (S := R) (fun V f hf => ?_) hR
  obtain ⟨s⟩ := hsections hf
  refine ⟨y.down • FreeAbelianGroup.of s, ?_⟩
  change (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj (Opposite.op V) =>
    (⟨1⟩ : ULift.{t} ℤ))) (y.down • FreeAbelianGroup.of s) = y
  rw [map_zsmul, FreeAbelianGroup.lift_apply_of]
  cases y with
  | up n =>
    apply ULift.ext
    change n * 1 = n
    simp

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The presheaf map induced by a compatible family of sections is an
isomorphism. -/
public lemma familyToTorsorHom_isIso (H : Sheaf J AddCommGrpCat.{t})
    (F : PseudoTorsor (C := C)
      (abelianSheafAsGroupSheaf (J := J) (C := C) H))
    (hF : F.IsTorsor) (s : ∀ U, F.presheaf.obj U)
    (hcompat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
      F.presheaf.map f (s U) = s V) :
    IsIso (familyToTorsorHom F s hcompat).hom := by
  let : ∀ U, IsIso ((familyToTorsorHom F s hcompat).hom.app U) := fun U => by
    rw [isIso_iff_bijective]
    change Function.Bijective (fun g => F.act U g (s U))
    exact action_bijective H F hF s U
  exact NatIso.isIso_of_isIso_app _

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- A torsor has the class of the trivial torsor exactly when it has a global
section. -/
public lemma torsor_class_eq_trivial_iff (H : Sheaf J AddCommGrpCat.{t})
    (F : AbelianTorsor H) :
    Quotient.mk (torsorSetoid H)
      ⟨trivialTorsor (abelianSheafAsGroupSheaf H),
        trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩ =
      Quotient.mk (torsorSetoid H) F ↔
      Nonempty (GlobalSections F.1.presheaf) := by
  rw [Quotient.eq]
  exact isTrivial_iff_nonempty_globalSections F.1 F.2

end Stacks.Cohomology.Torsors
