module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-! # Sections over a presheaf of sets along a full subsite, from a representable cover

Let `(C, J)` be a site and let `u : D ⥤ C` be a fully faithful functor, continuous and
cocontinuous for a topology `K` on `D`. For a presheaf of sets `P` on `C` and a sheaf `F` on `C`,
restriction along `u` sends a morphism `P ⟶ F` to a morphism `u^p P ⟶ u^p F` of presheaves on
`D`. This file proves that this restriction is injective as soon as `P` is covered by a
representable presheaf `h_{u(d)}` — that is, receives a locally surjective map from it — and
bijective as soon as moreover the presheaf of pairs of sections of `h_{u(d)}` with the same image
in `P` is itself covered by a representable presheaf. This is the degree-zero step of the
comparison of cohomology along a full subsite by Čech descent.

The presheaf of `(r + 1)`-tuples of sections with a common image, `tuplePresheaf`, is an
explicit model of the degree-`r` term of the Čech nerve of a map of presheaves of sets.

## Main definitions

* `Stacks.Sites.CoverDescent.tuplePresheaf`: for `t : A ⟶ P` and `r : ℕ`, the presheaf of
  `(r + 1)`-tuples of sections of `A` with a common image in `P`.
* `Stacks.Sites.CoverDescent.restrictHom`: restriction of morphisms of presheaves along `u`.

## Main results

* `Stacks.Sites.CoverDescent.hom_ext_of_isLocallySurjective`: a locally surjective map is an
  epimorphism onto sheaves.
* `Stacks.Sites.CoverDescent.exists_factor_of_isLocallySurjective`: a map out of the source of a
  locally surjective map to a sheaf factors through it as soon as it is constant on the fibres.
* `Stacks.Sites.CoverDescent.restrictHom_injective`: restriction is injective on morphisms out of
  a presheaf with a representable cover.
* `Stacks.Sites.CoverDescent.restrictHom_bijective`: restriction is bijective on morphisms out of
  a presheaf with a representable cover whose presheaf of pairs also has a representable
  cover.
* `Stacks.Sites.CoverDescent.restrictHom_bijective_uliftYoneda`: restriction is bijective on
  morphisms out of a representable presheaf `h_{u(d)}`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u₁ u₂

namespace Stacks.Sites.CoverDescent

variable {C : Type u₁} [Category.{v} C]

/-! ### Tuples of sections with a common image -/

section Tuple

variable {A P : Cᵒᵖ ⥤ Type w} (t : A ⟶ P)

/-- The presheaf of `(r + 1)`-tuples of sections of `A` with a common image under `t : A ⟶ P`.
It is the degree-`r` term of the Čech nerve of `t`, written out. -/
@[simps obj]
def tuplePresheaf (r : ℕ) : Cᵒᵖ ⥤ Type w where
  obj y := {a : Fin (r + 1) → A.obj y // ∀ i, t.app y (a i) = t.app y (a 0)}
  map g := ↾fun a => ⟨fun i => A.map g (a.1 i), fun i => by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, a.2 i]⟩
  map_id y := by
    apply TypeCat.homEquiv.injective
    funext a
    exact Subtype.ext (funext fun i => by simp)
  map_comp f g := by
    apply TypeCat.homEquiv.injective
    funext a
    exact Subtype.ext (funext fun i => by simp)

/-- The entries of the restriction of a tuple along `g` are the restrictions of its entries. -/
@[simp]
lemma tuplePresheaf_map_val (r : ℕ) {y y' : Cᵒᵖ} (g : y ⟶ y') (a : (tuplePresheaf t r).obj y)
    (i : Fin (r + 1)) : ((tuplePresheaf t r).map g a).1 i = A.map g (a.1 i) := rfl

/-- The projection of a tuple to one of its entries. -/
@[simps]
def tupleπ (r : ℕ) (i : Fin (r + 1)) : tuplePresheaf t r ⟶ A where
  app y := ↾fun a => a.1 i

end Tuple

/-! ### Locally surjective maps onto sheaves -/

section Sheaf

/-- Extensionality for morphisms of presheaves of sets, in terms of their values on sections. -/
lemma natTrans_ext {F G : Cᵒᵖ ⥤ Type w} {φ ψ : F ⟶ G}
    (h : ∀ (y : Cᵒᵖ) (p : F.obj y), φ.app y p = ψ.app y p) : φ = ψ := by
  ext y p
  exact h y p

variable (J : GrothendieckTopology C) {A P F : Cᵒᵖ ⥤ Type w} (t : A ⟶ P)

/-- **A locally surjective map is an epimorphism onto sheaves.** Two morphisms from `P` to a
sheaf which agree after precomposition with a locally surjective `t : A ⟶ P` agree. -/
@[sga "3 VIIA 8.1.4" "covering ⇒ epimorphism"]
lemma hom_ext_of_isLocallySurjective [Presheaf.IsLocallySurjective J t]
    (hF : Presieve.IsSheaf J F) {φ₁ φ₂ : P ⟶ F} (h : t ≫ φ₁ = t ≫ φ₂) : φ₁ = φ₂ := by
  refine natTrans_ext fun y p => ?_
  refine (hF _ (Presheaf.imageSieve_mem J t p)).isSeparatedFor.ext fun Z g hg => ?_
  obtain ⟨a, ha⟩ := hg
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  simpa only [NatTrans.comp_app_apply, ha] using congrArg (fun φ => φ.app (op Z) a) h

/-- **A map to a sheaf which is constant on the fibres of a locally surjective map factors
through it.** -/
lemma exists_factor_of_isLocallySurjective [Presheaf.IsLocallySurjective J t]
    (hF : Presieve.IsSheaf J F) (φ₀ : A ⟶ F)
    (hφ₀ : ∀ (y : Cᵒᵖ) (a a' : A.obj y), t.app y a = t.app y a' → φ₀.app y a = φ₀.app y a') :
    ∃ φ : P ⟶ F, t ≫ φ = φ₀ := by
  let fam : ∀ {y : C} (p : P.obj (op y)),
      Presieve.FamilyOfElements F (Presheaf.imageSieve t p).arrows :=
    fun p Z g hg => φ₀.app (op Z) (Presheaf.localPreimage t p g hg)
  have hcompat : ∀ {y : C} (p : P.obj (op y)), (fam p).Compatible := by
    intro y p Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    simp only [fam]
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    refine hφ₀ _ _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, Presheaf.app_localPreimage,
      Presheaf.app_localPreimage, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  let val : ∀ {y : C} (p : P.obj (op y)), F.obj (op y) := fun p =>
    (hF _ (Presheaf.imageSieve_mem J t p)).amalgamate (fam p) (hcompat p)
  have hval : ∀ {y : C} (p : P.obj (op y)) {Z : C} (g : Z ⟶ y) (a : A.obj (op Z)),
      t.app (op Z) a = P.map g.op p → F.map g.op (val p) = φ₀.app (op Z) a := by
    intro y p Z g a ha
    have hg : (Presheaf.imageSieve t p).arrows g := ⟨a, ha⟩
    rw [(hF _ (Presheaf.imageSieve_mem J t p)).valid_glue (hcompat p) g hg]
    exact hφ₀ _ _ _ ((Presheaf.app_localPreimage t p g hg).trans ha.symm)
  refine ⟨{ app := fun y => ↾fun p => val (y := y.unop) p, naturality := ?_ }, ?_⟩
  · intro y y' g
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    simp only [TypeCat.homEquiv_apply, types_comp_apply, TypeCat.ofHom_apply]
    refine (hF _ (Presheaf.imageSieve_mem J t (P.map g p))).isSeparatedFor.ext
      fun Z k hk => ?_
    obtain ⟨a, ha⟩ := hk
    have hka : t.app (op Z) a = P.map (k ≫ g.unop).op p := by
      rw [ha, op_comp, Functor.map_comp_apply]
      rfl
    rw [hval (P.map g p) k a ha, ← hval p (k ≫ g.unop) a hka, op_comp,
      Functor.map_comp_apply]
    rfl
  · refine natTrans_ext fun y a => ?_
    simp only [NatTrans.comp_app, types_comp_apply, TypeCat.ofHom_apply]
    simpa using hval (y := y.unop) (t.app y a) (𝟙 _) a (by simp)

end Sheaf

/-! ### Restriction along a functor -/

section Restriction

variable {D : Type u₂} [Category.{v} D] (u : D ⥤ C)

/-- Restriction of a morphism of presheaves along `u`. -/
abbrev restrictHom (P F : Cᵒᵖ ⥤ Type w) (φ : P ⟶ F) : u.op ⋙ P ⟶ u.op ⋙ F :=
  Functor.whiskerLeft u.op φ

/-- Restriction is compatible with composition. -/
lemma restrictHom_comp {P Q F : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) (φ : Q ⟶ F) :
    restrictHom u P F (f ≫ φ) = Functor.whiskerLeft u.op f ≫ restrictHom u Q F φ := rfl

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **Restriction along `u` is injective on morphisms out of a presheaf covered by one on which
it is injective.** If `t : A ⟶ P` is locally surjective, `F` is a sheaf and restriction along
`u` is injective on morphisms `A ⟶ F`, then it is injective on morphisms `P ⟶ F`: two
morphisms out of `P` with the same restriction agree after `t`, hence agree. -/
lemma restrictHom_injective_of_isLocallySurjective {A P : Cᵒᵖ ⥤ Type w} (t : A ⟶ P)
    [Presheaf.IsLocallySurjective J t] (F : Cᵒᵖ ⥤ Type w) (hF : Presieve.IsSheaf J F)
    (hA : Function.Injective (restrictHom u A F)) :
    Function.Injective (restrictHom u P F) := fun φ₁ φ₂ h =>
  hom_ext_of_isLocallySurjective J t hF (hA (by rw [restrictHom_comp, restrictHom_comp, h]))

/-- Restriction along `u` is injective on morphisms out of `P` exactly when it is on morphisms
out of a presheaf isomorphic to `P`. -/
lemma restrictHom_injective_of_iso {P Q : Cᵒᵖ ⥤ Type w} (e : P ≅ Q) (F : Cᵒᵖ ⥤ Type w)
    (hQ : Function.Injective (restrictHom u Q F)) : Function.Injective (restrictHom u P F) :=
  fun φ₁ φ₂ h => by
    have h' : restrictHom u Q F (e.inv ≫ φ₁) = restrictHom u Q F (e.inv ≫ φ₂) := by
      rw [restrictHom_comp, restrictHom_comp, h]
    simpa using congrArg (fun φ => e.hom ≫ φ) (hQ h')

/-- Restriction along `u` is bijective on morphisms out of `P` as soon as it is on morphisms out
of a presheaf isomorphic to `P`. -/
lemma restrictHom_bijective_of_iso {P Q : Cᵒᵖ ⥤ Type w} (e : P ≅ Q) (F : Cᵒᵖ ⥤ Type w)
    (hQ : Function.Bijective (restrictHom u Q F)) : Function.Bijective (restrictHom u P F) := by
  refine ⟨restrictHom_injective_of_iso u e F hQ.1, fun ψ => ?_⟩
  obtain ⟨φ, hφ⟩ := hQ.2 (Functor.whiskerLeft u.op e.inv ≫ ψ)
  refine ⟨e.hom ≫ φ, ?_⟩
  rw [restrictHom_comp, hφ, ← Category.assoc, ← Functor.whiskerLeft_comp, e.hom_inv_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- **Restriction along `u` is bijective on morphisms out of a presheaf covered by one on which
it is bijective.** Let `t : A ⟶ P` be locally surjective, and suppose its restriction to `D` is
locally surjective too. If restriction to `D` is bijective on morphisms `A ⟶ F` into a sheaf
`F` and injective on morphisms out of the presheaf of pairs of sections of `A` with the same
image in `P`, then it is bijective on morphisms `P ⟶ F`.

Injectivity: two morphisms out of `P` with the same restriction agree after `t`, hence agree.
Surjectivity: a morphism `ψ : u^p P ⟶ u^p F` gives `(u^p t) ≫ ψ`, which is the restriction of a
morphism `φ₀ : A ⟶ F`; the two composites of `φ₀` with the projections of the presheaf of pairs
have the same restriction, hence agree, so `φ₀` factors through `t`; and the factorization
restricts to `ψ` because `u^p t` is locally surjective. -/
lemma restrictHom_bijective_of_isLocallySurjective [u.IsContinuous K J] {A P : Cᵒᵖ ⥤ Type w}
    (t : A ⟶ P) [Presheaf.IsLocallySurjective J t]
    [Presheaf.IsLocallySurjective K (Functor.whiskerLeft u.op t)]
    (F : Cᵒᵖ ⥤ Type w) (hF : Presieve.IsSheaf J F)
    (hA : Function.Bijective (restrictHom u A F))
    (hA₁ : Function.Injective (restrictHom u (tuplePresheaf t 1) F)) :
    Function.Bijective (restrictHom u P F) := by
  have hsheaf : Presieve.IsSheaf K (u.op ⋙ F) := u.op_comp_isSheaf_of_isSheaf_type K hF
  refine ⟨restrictHom_injective_of_isLocallySurjective u J t F hF hA.1, fun ψ => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA.2 (Functor.whiskerLeft u.op t ≫ ψ)
  have hpair : tupleπ t 1 0 ≫ φ₀ = tupleπ t 1 1 ≫ φ₀ := by
    refine hA₁ ?_
    rw [restrictHom_comp, restrictHom_comp, hφ₀]
    refine natTrans_ext fun y a => ?_
    simp only [NatTrans.comp_app_apply, Functor.whiskerLeft_app, tupleπ_app,
      TypeCat.ofHom_apply]
    rw [a.2 1]
  obtain ⟨φ, hφ⟩ := exists_factor_of_isLocallySurjective J t hF φ₀ fun y a a' h => by
    have := congrArg (fun φ => φ.app y ⟨![a, a'], Fin.forall_fin_two.2 ⟨rfl, h.symm⟩⟩) hpair
    simp only [NatTrans.comp_app, tupleπ_app] at this
    exact this
  refine ⟨φ, hom_ext_of_isLocallySurjective K (Functor.whiskerLeft u.op t) hsheaf ?_⟩
  rw [← restrictHom_comp, hφ, hφ₀]

/-- **Restriction along a full functor is bijective on morphisms out of a representable
presheaf `h_{u(d)}`.** Both sides are the sections of the target over `u(d)`: on the left by the
Yoneda lemma, on the right because every section of `h_{u(d)}` over an object of `D` is, by
fullness, the image of a morphism of `D`. -/
lemma restrictHom_bijective_uliftYoneda [u.Full] (d : D) (F : Cᵒᵖ ⥤ Type (max v w)) :
    Function.Bijective (restrictHom u (uliftYoneda.{w}.obj (u.obj d)) F) := by
  refine ⟨fun φ₁ φ₂ h => uliftYonedaEquiv.injective ?_, fun ψ => ?_⟩
  · exact congrArg (fun ψ => ψ.app (op d) (ULift.up (𝟙 _))) h
  refine ⟨uliftYonedaEquiv.symm (ψ.app (op d) (ULift.up (𝟙 _))), natTrans_ext fun y a => ?_⟩
  obtain ⟨d'⟩ := y
  obtain ⟨a⟩ := a
  obtain ⟨b, rfl⟩ := u.map_surjective a
  have hψ := NatTrans.naturality_apply ψ b.op
    (ULift.up (𝟙 (u.obj d)) : (uliftYoneda.{w}.obj (u.obj d)).obj (op (u.obj d)))
  have h₁ : (u.op ⋙ uliftYoneda.{w}.obj (u.obj d)).map b.op
      (ULift.up (𝟙 (u.obj d)) : (uliftYoneda.{w}.obj (u.obj d)).obj (op (u.obj d))) =
      ULift.up (u.map b) := by
    simp
  rw [h₁] at hψ
  exact hψ.symm

end Restriction

/-! ### Fibre products of presheaves of sets -/

section FibreProduct

variable {F G H : Cᵒᵖ ⥤ Type w} (f : F ⟶ H) (g : G ⟶ H)

/-- The fibre product of two morphisms of presheaves of sets, written out sectionwise. -/
@[simps obj]
def fibreProductPresheaf : Cᵒᵖ ⥤ Type w where
  obj y := {x : F.obj y × G.obj y // f.app y x.1 = g.app y x.2}
  map h := ↾fun x => ⟨(F.map h x.1.1, G.map h x.1.2), by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, x.2]⟩
  map_id y := by
    apply TypeCat.homEquiv.injective
    funext x
    exact Subtype.ext (Prod.ext (by simp) (by simp))
  map_comp h h' := by
    apply TypeCat.homEquiv.injective
    funext x
    exact Subtype.ext (Prod.ext (by simp) (by simp))

/-- Prepending an entry identifies the tuples of length `r + 2` with the fibre product of the
source of `t` and the tuples of length `r + 1`, over the target of `t`. -/
def tuplePresheafSuccIso {A P : Cᵒᵖ ⥤ Type w} (t : A ⟶ P) (r : ℕ) :
    tuplePresheaf t (r + 1) ≅ fibreProductPresheaf t (tupleπ t r 0 ≫ t) where
  hom :=
    { app := fun y => ↾fun a => ⟨(a.1 0,
        ⟨Fin.tail a.1, fun i => (a.2 i.succ).trans (a.2 1).symm⟩), (a.2 1).symm⟩
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun y => ↾fun x => ⟨Fin.cons x.1.1 x.1.2.1, fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact (x.1.2.2 j).trans x.2.symm⟩
      naturality := fun _ _ h => TypeCat.homEquiv.injective (funext fun x => Subtype.ext
        (funext fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> rfl)) }
  hom_inv_id := natTrans_ext fun y a => Subtype.ext (funext fun i => by
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl)
  inv_hom_id := natTrans_ext fun y x =>
    Subtype.ext (Prod.ext rfl (Subtype.ext (funext fun i => rfl)))

/-- A morphism into the fibre product presheaf, from two morphisms agreeing over the base. -/
@[simps]
def fibreProductLift {Q : Cᵒᵖ ⥤ Type w} (a : Q ⟶ F) (b : Q ⟶ G) (h : a ≫ f = b ≫ g) :
    Q ⟶ fibreProductPresheaf f g where
  app y := ↾fun x => ⟨(a.app y x, b.app y x), by
    simpa using congrArg (fun φ => φ.app y x) h⟩
  naturality y y' k := TypeCat.homEquiv.injective (funext fun x => Subtype.ext (Prod.ext
    (by exact NatTrans.naturality_apply a k x) (by exact NatTrans.naturality_apply b k x)))

/-- The fibre product presheaf is unchanged when its second factor is replaced by an isomorphic
one over the base. -/
@[simps]
def fibreProductPresheafIsoOfIso {G' : Cᵒᵖ ⥤ Type w} (g' : G' ⟶ H) (E : G ≅ G')
    (hE : E.hom ≫ g' = g) : fibreProductPresheaf f g ≅ fibreProductPresheaf f g' where
  hom :=
    { app := fun y => ↾fun x => ⟨(x.1.1, E.hom.app y x.1.2), by
        rw [x.2, ← NatTrans.comp_app_apply, hE]⟩
      naturality := fun _ _ k => TypeCat.homEquiv.injective (funext fun x => Subtype.ext
        (Prod.ext rfl (by exact NatTrans.naturality_apply E.hom k x.1.2))) }
  inv :=
    { app := fun y => ↾fun x => ⟨(x.1.1, E.inv.app y x.1.2), by
        rw [x.2, ← hE, NatTrans.comp_app_apply]
        simp⟩
      naturality := fun _ _ k => TypeCat.homEquiv.injective (funext fun x => Subtype.ext
        (Prod.ext rfl (by exact NatTrans.naturality_apply E.inv k x.1.2))) }
  hom_inv_id := natTrans_ext fun y x => Subtype.ext (Prod.ext rfl
    (by exact Iso.hom_inv_id_app_apply E y x.1.2))
  inv_hom_id := natTrans_ext fun y x => Subtype.ext (Prod.ext rfl
    (by exact Iso.inv_hom_id_app_apply E y x.1.2))

end FibreProduct

/-- The tuple presheaves of a map of presheaves are unchanged when the map is composed on either
side with isomorphisms. -/
@[simps]
def tuplePresheafCompIso {A A' P P' : Cᵒᵖ ⥤ Type w} (e₀ : A ≅ A') (t' : A' ⟶ P')
    (e₁ : P' ≅ P) (r : ℕ) :
    tuplePresheaf (e₀.hom ≫ t' ≫ e₁.hom) r ≅ tuplePresheaf t' r where
  hom :=
    { app := fun y => ↾fun a => ⟨fun i => e₀.hom.app y (a.1 i), fun i => by
        have h := a.2 i
        simp only [NatTrans.comp_app, types_comp_apply] at h
        exact (e₁.app y).toEquiv.injective h⟩
      naturality := fun _ _ k => TypeCat.homEquiv.injective (funext fun a => Subtype.ext
        (funext fun i => by exact NatTrans.naturality_apply e₀.hom k (a.1 i))) }
  inv :=
    { app := fun y => ↾fun a => ⟨fun i => e₀.inv.app y (a.1 i), fun i => by
        simp only [NatTrans.comp_app, types_comp_apply, Iso.inv_hom_id_app_apply]
        rw [a.2 i]⟩
      naturality := fun _ _ k => TypeCat.homEquiv.injective (funext fun a => Subtype.ext
        (funext fun i => by exact NatTrans.naturality_apply e₀.inv k (a.1 i))) }
  hom_inv_id := natTrans_ext fun y a => Subtype.ext (funext fun i => by
    exact Iso.hom_inv_id_app_apply e₀ y (a.1 i))
  inv_hom_id := natTrans_ext fun y a => Subtype.ext (funext fun i => by
    exact Iso.inv_hom_id_app_apply e₀ y (a.1 i))

end Stacks.Sites.CoverDescent

end
