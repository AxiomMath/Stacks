module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Transporting a set-level comparison of sections to abelian groups

Statements turning a description of the underlying sets of sections of a sheaf of abelian groups
into a description of the sections as abelian groups, and two facts about the site of opens of a
topological space.

All names are in the namespace `CategoryTheory`.

## Main definitions

* `liftNatIsoAb`: an isomorphism of the underlying `Type`-valued functors of two additive functors
  into abelian groups, as an isomorphism of functors into abelian groups.
* `constantZHomEquiv`: natural transformations out of the constant functor at `ULift ℤ` into an
  abelian presheaf are the natural transformations out of the constant functor at a singleton into
  its underlying presheaf of sets.
* `supportedSectionsEquiv`: for an adjunction `i ⊣ j` and a subsingleton-valued presheaf `P` with
  a section over every object in the image of `i`, over whose sections the counit is invertible,
  morphisms out of `P` are the morphisms out of the terminal presheaf after restriction along `i`.
* `topPullbackYoneda`: the inverse image along a continuous map of the sheaf represented by an
  open is the sheaf represented by its preimage.

## Main results

* `natTrans_forget_additive`: a natural transformation of the underlying `Type`-valued functors
  of two additive functors into abelian groups is additive.
* `constantZHomEquiv_naturality`, `constantZHomEquiv_symm_naturality`,
  `supportedSectionsEquiv_naturality`: these equivalences are natural in the target.
* `opens_subcanonical`: the site of opens of a topological space is subcanonical.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u

namespace CategoryTheory

/-- A natural transformation of the underlying `Type`-valued functors of two additive functors
into abelian groups is additive at every object. -/
theorem natTrans_forget_additive {C : Type u} [Category.{v} C]
    [Preadditive C] [HasBinaryBiproducts C]
    {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]
    (e : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) (X : C)
    (x y : F.obj X) : e.app X (x + y) = e.app X x + e.app X y := by
  let z := F.map (biprod.inl : X ⟶ X ⊞ X) x + F.map biprod.inr y
  have hx : F.map (biprod.fst : X ⊞ X ⟶ X) z = x := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have hy : F.map (biprod.snd : X ⊞ X ⟶ X) z = y := by
    simp [z, ← ConcreteCategory.comp_apply, ← F.map_comp]
  have ha : F.map ((biprod.fst : X ⊞ X ⟶ X) + biprod.snd) z = x + y := by
    simp [F.map_add, hx, hy]
  have hn := ConcreteCategory.congr_hom
    (e.naturality ((biprod.fst : X ⊞ X ⟶ X) + biprod.snd)) z
  change e.app X (F.map _ z) = G.map _ (e.app (X ⊞ X) z) at hn
  rw [ha] at hn
  rw [hn, G.map_add]
  change G.map biprod.fst (e.app (X ⊞ X) z) +
    G.map biprod.snd (e.app (X ⊞ X) z) = _
  have hn₁ := ConcreteCategory.congr_hom (e.naturality (biprod.fst : X ⊞ X ⟶ X)) z
  have hn₂ := ConcreteCategory.congr_hom (e.naturality (biprod.snd : X ⊞ X ⟶ X)) z
  change e.app X (F.map _ z) = G.map _ (e.app (X ⊞ X) z) at hn₁ hn₂
  rw [← hn₁, ← hn₂, hx, hy]
  rfl

/-- **An isomorphism of the underlying `Type`-valued functors of two additive functors into
abelian groups is an isomorphism of functors into abelian groups.** -/
def liftNatIsoAb {C : Type u} [Category.{v} C]
    [Preadditive C] [HasBinaryBiproducts C]
    {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]
    (e : F ⋙ forget AddCommGrpCat ≅ G ⋙ forget AddCommGrpCat) : F ≅ G :=
  NatIso.ofComponents (fun X =>
    (AddEquiv.mk' (e.app X).toEquiv (natTrans_forget_additive e.hom X)).toAddCommGrpIso)
    (by intro X Y f; ext x; exact ConcreteCategory.congr_hom (e.hom.naturality f) x)

/-- **Natural transformations out of the constant functor at `ULift ℤ` into an abelian presheaf
are the natural transformations out of the constant functor at a singleton into its underlying
presheaf of sets.** -/
def constantZHomEquiv {C : Type u} [Category.{v} C] (F : C ⥤ AddCommGrpCat.{w}) :
    ((Functor.const C).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) ≃
      ((Functor.const C).obj PUnit ⟶ F ⋙ forget AddCommGrpCat) where
  toFun t :=
    { app W := ↾fun _ => AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W) (t.app W)
      naturality := by
        intro W V f
        ext p
        exact ConcreteCategory.congr_hom (t.naturality f) (ULift.up (1 : ℤ)) }
  invFun t :=
    { app W := (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm (t.app W PUnit.unit)
      naturality := by
        intro W V f
        apply (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj V)).injective
        change AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj V)
          ((AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj V)).symm _) = _
        rw [AddEquiv.apply_symm_apply]
        have h := ConcreteCategory.congr_hom (t.naturality f) PUnit.unit
        dsimp at h
        change t.app V PUnit.unit = F.map f
          (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)
            ((AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm _))
        rw [AddEquiv.apply_symm_apply]
        exact h }
  left_inv t := NatTrans.ext <| funext fun W =>
    (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm_apply_apply _
  right_inv t := by
    ext W p
    exact (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).apply_symm_apply _

/-- `constantZHomEquiv` is natural in the abelian presheaf. -/
theorem constantZHomEquiv_naturality
    {C : Type u} [Category.{v} C] {F G : C ⥤ AddCommGrpCat.{w}}
    (t : (Functor.const C).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) (f : F ⟶ G) :
    constantZHomEquiv G (t ≫ f) = constantZHomEquiv F t ≫
      Functor.whiskerRight f (forget AddCommGrpCat.{w}) := by
  ext W p
  rfl

/-- The inverse of `constantZHomEquiv` is natural in the abelian presheaf. -/
theorem constantZHomEquiv_symm_naturality
    {C : Type u} [Category.{v} C] {F G : C ⥤ AddCommGrpCat.{w}}
    (t : (Functor.const C).obj PUnit ⟶ F ⋙ forget AddCommGrpCat.{w}) (f : F ⟶ G) :
    (constantZHomEquiv G).symm (t ≫ Functor.whiskerRight f (forget AddCommGrpCat.{w})) =
      (constantZHomEquiv F).symm t ≫ f := by
  apply (constantZHomEquiv G).injective
  rw [Equiv.apply_symm_apply, constantZHomEquiv_naturality, Equiv.apply_symm_apply]

/-- **Morphisms out of a support presheaf.** Let `i ⊣ j` be an adjunction between the underlying
categories of two sites, let `P` be a presheaf on the target whose values are subsingletons,
which has a chosen section over every object in the image of `i`, and over whose sections the
counit of the adjunction is invertible.  Then morphisms `P ⟶ F` correspond to morphisms from the
terminal presheaf into the restriction of `F` along `i`. -/
noncomputable def supportedSectionsEquiv
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (i : C ⥤ D) (j : D ⥤ C) (ad : i ⊣ j)
    (P : Dᵒᵖ ⥤ Type w) (F : Dᵒᵖ ⥤ Type w)
    (hP : ∀ W, Subsingleton (P.obj W))
    (s : ∀ W, P.obj (op (i.obj W)))
    (hc : ∀ W, P.obj (op W) → IsIso (ad.counit.app W)) :
    (P ⟶ F) ≃ ((Functor.const Cᵒᵖ).obj PUnit ⟶ i.op ⋙ F) := by
  let forward (t : P ⟶ F) : (Functor.const Cᵒᵖ).obj PUnit ⟶ i.op ⋙ F :=
    { app W := ↾fun _ => t.app _ (s W.unop)
      naturality := by
        intro W V f
        ext x
        have e := ConcreteCategory.congr_hom (t.naturality (i.op.map f)) (s W.unop)
        dsimp at e ⊢
        exact (congrArg (t.app _) ((hP _).elim _ _)).trans e }
  let backward (t : (Functor.const Cᵒᵖ).obj PUnit ⟶ i.op ⋙ F) : P ⟶ F :=
    { app W := ↾fun p => by
        letI := hc W.unop p
        exact F.map (inv (ad.counit.app W.unop)).op (t.app (op (j.obj W.unop)) PUnit.unit)
      naturality := by
        intro W V f
        ext p
        let := hc W.unop p
        let := hc V.unop (P.map f p)
        dsimp
        have hn := ConcreteCategory.congr_hom (t.naturality (j.map f.unop).op) PUnit.unit
        dsimp at hn
        rw [hn, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
        apply congrArg (fun k => F.map k (t.app (op (j.obj W.unop)) PUnit.unit))
        apply Quiver.Hom.unop_inj
        dsimp
        apply (cancel_mono (ad.counit.app W.unop)).mp
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        have hcn : i.map (j.map f.unop) ≫ ad.counit.app W.unop =
            ad.counit.app V.unop ≫ f.unop := ad.counit.naturality f.unop
        rw [hcn]
        simp }
  refine ⟨forward, backward, ?_, ?_⟩
  · intro t
    ext W p
    let := hc W.unop p
    change F.map (inv (ad.counit.app W.unop)).op
      (t.app (op (i.obj (j.obj W.unop))) (s (j.obj W.unop))) = t.app W p
    have hn := ConcreteCategory.congr_hom
      (t.naturality (inv (ad.counit.app W.unop)).op) (s (j.obj W.unop))
    exact hn.symm.trans (congrArg (t.app W) ((hP W).elim _ _))
  · intro t
    ext W p
    let := hc (i.obj W.unop) (s W.unop)
    change F.map (inv (ad.counit.app (i.obj W.unop))).op
      (t.app (op (j.obj (i.obj W.unop))) PUnit.unit) = t.app W p
    have hi : inv (ad.counit.app (i.obj W.unop)) = i.map (ad.unit.app W.unop) :=
      IsIso.inv_eq_of_inv_hom_id (ad.left_triangle_components W.unop)
    rw [hi]
    exact (ConcreteCategory.congr_hom (t.naturality (ad.unit.app W.unop).op) p).symm

/-- `supportedSectionsEquiv` is natural in the target presheaf. -/
theorem supportedSectionsEquiv_naturality
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (i : C ⥤ D) (j : D ⥤ C) (ad : i ⊣ j)
    (P : Dᵒᵖ ⥤ Type w) {F G : Dᵒᵖ ⥤ Type w}
    (hP : ∀ W, Subsingleton (P.obj W))
    (s : ∀ W, P.obj (op (i.obj W)))
    (hc : ∀ W, P.obj (op W) → IsIso (ad.counit.app W))
    (t : P ⟶ F) (f : F ⟶ G) :
    supportedSectionsEquiv i j ad P G hP s hc (t ≫ f) =
      supportedSectionsEquiv i j ad P F hP s hc t ≫ Functor.whiskerLeft i.op f := by
  ext W p
  rfl

/-- **The site of opens of a topological space is subcanonical.** -/
theorem opens_subcanonical (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun V => ?_
  intro U S hS t ht
  refine ⟨homOfLE ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨W, f, hf, hxW⟩ := hS x hx
    exact (t f hf).le hxW
  · intro W f hf
    apply Subsingleton.elim (α := _ ⟶ V)
  · intro y hy
    apply Subsingleton.elim (α := _ ⟶ V)

attribute [local instance] opens_subcanonical

/-- **The inverse image along a continuous map of the sheaf represented by an open is the sheaf
represented by its preimage.** -/
noncomputable def topPullbackYoneda {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y) :
    (TopCat.Sheaf.pullback (Type u) f).obj ((Opens.grothendieckTopology Y).yoneda.obj V) ≅
      (Opens.grothendieckTopology X).yoneda.obj ((Opens.map f).obj V) := by
  let e (G : TopCat.Sheaf (Type u) X) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv
        ((Opens.grothendieckTopology Y).yoneda.obj V) G).trans
      ((Opens.grothendieckTopology Y).yonedaEquiv.trans
        (Opens.grothendieckTopology X).yonedaEquiv.symm)
  exact Coyoneda.ext _ _ (fun {G} => e G) (fun {G} => (e G).symm)
    (fun _ => (e _).symm_apply_apply _) (fun _ => (e _).apply_symm_apply _) (by
      intro G H s t
      have h1 := (Opens.grothendieckTopology (Y : TopCat)).yonedaEquiv_symm_naturality_right V
        ((TopCat.Sheaf.pushforward (Type u) f).map t)
        ((Opens.grothendieckTopology (X : TopCat)).yonedaEquiv s)
      have h2 :=
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv_naturality_right_symm
          ((Opens.grothendieckTopology (Y : TopCat)).yonedaEquiv.symm
            ((Opens.grothendieckTopology (X : TopCat)).yonedaEquiv s)) t
      change ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv _ H).symm
        ((Opens.grothendieckTopology Y).yonedaEquiv.symm
          (((TopCat.Sheaf.pushforward (Type u) f).map t).hom.app (op V)
            ((Opens.grothendieckTopology X).yonedaEquiv s))) = _
      exact (congrArg (fun z =>
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).homEquiv
          ((Opens.grothendieckTopology Y).yoneda.obj V) H).symm z) h1.symm).trans h2)

end CategoryTheory

end
