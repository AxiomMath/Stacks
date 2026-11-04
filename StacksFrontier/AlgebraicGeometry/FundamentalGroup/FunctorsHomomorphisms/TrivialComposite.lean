module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Trivial composites in Galois categories

For two successive functors of Galois categories, the composite of the associated
homomorphisms of fundamental groups is trivial exactly when the composite functor takes every
object to a finite coproduct of final objects.

## Main definitions

* `CategoryTheory.IsFiniteCoproductOfTerminal` says that an object is a finite coproduct of
  terminal objects.

## Main results

* `CategoryTheory.comp_hom_eq_one_iff_forall_isFiniteCoproductOfTerminal` characterizes
  triviality of the composite homomorphism by the essential image of the composite functor.

## Implementation notes

A finite coproduct is presented by a colimit cocone indexed by `Fin n`. Thus the formulation
also includes the empty coproduct. The two 2-commutative squares from the functoriality theorem
are retained explicitly as `GaloisFunctorData`; their homomorphisms are the `h` and `h'` of the
source.

## References

* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' u'' v'' w

namespace CategoryTheory

/-- An object which is a coproduct of finitely many terminal objects. -/
public def IsFiniteCoproductOfTerminal {C : Type u} [Category.{v} C] (X : C) : Prop :=
  ∃ (n : ℕ) (A : Fin n → C) (f : (i : Fin n) → A i ⟶ X),
    (∀ i, Nonempty (IsTerminal (A i))) ∧ Nonempty (IsColimit (Cofan.mk X f))

private theorem terminal_iff_unique {C : Type u} [Category.{v, u} C]
    (F : C ⥤ FintypeCat.{w}) [CategoryTheory.GaloisCategory C]
    [CategoryTheory.PreGaloisCategory.FiberFunctor F] (Z : C) :
    Nonempty (IsTerminal Z) ↔ Nonempty (Unique ((F.obj Z).obj)) := by
  let G := F ⋙ FintypeCat.incl
  constructor
  · intro hZ
    let : PreservesLimit (Functor.empty.{0} C) G := inferInstance
    exact ⟨Types.isTerminalEquivUnique (G.obj Z) (IsTerminal.isTerminalObj G Z hZ.some)⟩
  · intro hFZ
    let : Unique (G.obj Z) := hFZ.some
    let : HasTerminal C := inferInstance
    let T : C := ⊤_ C
    have hT : IsTerminal T := terminalIsTerminal
    let : PreservesLimit (Functor.empty.{0} C) G := inferInstance
    have hFT : IsTerminal (G.obj T) := hT.isTerminalObj G T
    let : Unique (G.obj T) := Types.isTerminalEquivUnique (G.obj T) hFT
    let f : Z ⟶ T := terminal.from Z
    have hmap : IsIso (G.map f) := (isIso_iff_bijective (G.map f)).2
      ⟨(fun _ _ _ => Subsingleton.elim _ _), (fun y => ⟨default, Subsingleton.elim _ _⟩)⟩
    have hf : IsIso f := isIso_of_reflects_iso f G
    exact ⟨hT.ofIso (asIso f).symm⟩
private theorem finiteCoproductTerminal_iff_trivialAction {C : Type u} [Category.{v, u} C]
    (F : C ⥤ FintypeCat.{w}) [CategoryTheory.GaloisCategory C]
    [CategoryTheory.PreGaloisCategory.FiberFunctor F] (X : C) :
    IsFiniteCoproductOfTerminal X ↔ ∀ (σ : Aut F) (x : (F.obj X).obj), σ.hom.app X x = x := by
  constructor
  · rintro ⟨n, A, f, hterm, ⟨hc⟩⟩ σ x
    let G := F ⋙ FintypeCat.incl
    let hcf := isColimitOfPreserves G hc
    obtain ⟨⟨i⟩, y, rfl⟩ := Concrete.isColimit_exists_rep _ hcf x
    obtain ⟨_⟩ := (terminal_iff_unique F (A i)).mp (hterm i)
    calc
      σ.hom.app X (F.map (f i) y) = F.map (f i) (σ.hom.app (A i) y) :=
        NatTrans.naturality_apply σ.hom (f i) y
      _ = F.map (f i) y := by rw [Subsingleton.elim (σ.hom.app (A i) y) y]
  · intro htriv
    obtain ⟨ι, A, f, hc, hconn, hfin⟩ := PreGaloisCategory.has_decomp_connected_components X
    let G := F ⋙ FintypeCat.incl
    let : Fintype ι := Fintype.ofFinite ι
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let A' : Fin (Fintype.card ι) → C := A ∘ e
    let f' : (i : Fin (Fintype.card ι)) → A' i ⟶ X := fun i => f (e i)
    have hc' : IsColimit (Cofan.mk X f') :=
      (Cofan.isColimitEquivOfEquiv e (Cofan.mk X f)).toFun hc
    refine ⟨Fintype.card ι, A', f', fun i => ?_, ⟨hc'⟩⟩
    let : PreGaloisCategory.IsConnected (A' i) := hconn (e i)
    have hcG : IsColimit (Cofan.mk (G.obj X) (fun i => G.map (f' i))) :=
      (Cofan.isColimitMapCoconeEquiv G A' (Cofan.mk X f')).toFun (isColimitOfPreserves G hc')
    have hinj := Cofan.inj_injective_of_isColimit hcG i
    have hsub : Subsingleton ((F.obj (A' i)).obj) := ⟨fun a b => by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) a b
      have hσapp : σ.hom.app (A' i) a = b := by
        simpa [CategoryTheory.PreGaloisCategory.mulAction_def] using hσ
      have hh : F.map (f' i) a = F.map (f' i) b := by
        calc
          F.map (f' i) a = σ.hom.app X (F.map (f' i) a) := (htriv σ (F.map (f' i) a)).symm
          _ = F.map (f' i) (σ.hom.app (A' i) a) := NatTrans.naturality_apply σ.hom (f' i) a
          _ = F.map (f' i) b := by rw [hσapp]
      exact hinj hh⟩
    obtain ⟨a⟩ : Nonempty ((F.obj (A' i)).obj) := inferInstance
    exact (terminal_iff_unique F (A' i)).mpr ⟨⟨⟨a⟩, fun b => hsub.elim _ _⟩⟩
/-- The underlying map of the action isomorphism of a Galois functor datum is bijective. -/
private theorem bijective_hom_actionIso {C : Type u} [Category.{v} C] {C' : Type u'}
    [Category.{v'} C'] {F : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}} {H : C ⥤ C'}
    {t : H ⋙ F' ≅ F} (d : GaloisFunctorData F F' H t) (X : C) :
    Function.Bijective (ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom) := by
  let U : ContAction FintypeCat (Aut F') ⥤ FintypeCat :=
    forget₂ _ (Action FintypeCat (Aut F')) ⋙ forget₂ _ FintypeCat
  have : IsIso (U.map (d.actionIso.hom.app X)) := Functor.map_isIso U _
  have : IsIso (FintypeCat.incl.map (U.map (d.actionIso.hom.app X))) := Functor.map_isIso _ _
  change Function.Bijective (FintypeCat.incl.map (U.map (d.actionIso.hom.app X)))
  exact (isIso_iff_bijective _).mp inferInstance

section ActionBridge
variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {C'' : Type u''} [Category.{v''} C'']
variable (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w}) (F'' : C'' ⥤ FintypeCat.{w})
variable (H : C ⥤ C') (H' : C' ⥤ C'')
variable (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
variable (d : GaloisFunctorData F F' H t) (d' : GaloisFunctorData F' F'' H' t')
variable [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
variable [GaloisCategory C'] [PreGaloisCategory.FiberFunctor F']
variable [GaloisCategory C''] [PreGaloisCategory.FiberFunctor F'']

omit [GaloisCategory C] [PreGaloisCategory.FiberFunctor F] [GaloisCategory C']
  [PreGaloisCategory.FiberFunctor F'] in
private theorem h1 (X : C) (s : Aut F') (x : F.obj X) :
    (ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom)
        ((ConcreteCategory.hom ((d.hom.toMonoidHom s).hom.app X)) x) =
      (ConcreteCategory.hom (s.hom.app (H.obj X)))
        ((ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom) x) := by
  have h := (d.actionIso.hom.app X).hom.comm s
  have heval := ConcreteCategory.congr_hom h x
  let src :=
    ((PreGaloisCategory.functorToContAction F ⋙ ContAction.res FintypeCat d.hom).obj X).obj
  have hsrc : (ConcreteCategory.hom (src.ρ s)) x =
      (ConcreteCategory.hom ((d.hom.toMonoidHom s).hom.app X)) x := rfl
  have htgt (y : F'.obj (H.obj X)) :
      (ConcreteCategory.hom (((H ⋙ PreGaloisCategory.functorToContAction F').obj X).obj.ρ s)) y =
      (ConcreteCategory.hom (s.hom.app (H.obj X))) y := rfl
  have hc₁ := FintypeCat.comp_apply (src.ρ s) (d.actionIso.hom.app X).hom.hom x
  have hc₂ := FintypeCat.comp_apply (d.actionIso.hom.app X).hom.hom
    (((H ⋙ PreGaloisCategory.functorToContAction F').obj X).obj.ρ s) x
  rw [hc₁, hc₂] at heval
  rw [hsrc, htgt ((ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom) x)] at heval
  exact heval

omit [GaloisCategory C] [PreGaloisCategory.FiberFunctor F] [GaloisCategory C']
  [PreGaloisCategory.FiberFunctor F'] [GaloisCategory C'']
  [PreGaloisCategory.FiberFunctor F''] in
private theorem hcomp (X : C) (s : Aut F'') (x : F.obj X) :
    (ConcreteCategory.hom (d'.actionIso.hom.app (H.obj X)).hom.hom)
      ((ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom)
        ((ConcreteCategory.hom ((d.hom.toMonoidHom.comp d'.hom.toMonoidHom s).hom.app X)) x)) =
    (ConcreteCategory.hom (s.hom.app (H'.obj (H.obj X))))
      ((ConcreteCategory.hom (d'.actionIso.hom.app (H.obj X)).hom.hom)
        ((ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom) x)) :=
  (congrArg (ConcreteCategory.hom (d'.actionIso.hom.app (H.obj X)).hom.hom)
    (h1 F F' H t d X (d'.hom.toMonoidHom s) x)).trans
    (h1 F' F'' H' t' d' (H.obj X) s
      (ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom x))
end ActionBridge

/-- The composite homomorphism associated to two successive functors of Galois categories is
trivial exactly when every object in the image of the composite functor is a finite coproduct of
terminal objects. -/
@[stacks 0BS8, sga "1 V 6.5"]
public theorem comp_hom_eq_one_iff_forall_isFiniteCoproductOfTerminal
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {C'' : Type u''} [Category.{v''} C'']
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (d : GaloisFunctorData F F' H t)
    (d' : GaloisFunctorData F' F'' H' t') :
    d.hom.toMonoidHom.comp d'.hom.toMonoidHom = 1 ↔
      ∀ X : C, IsFiniteCoproductOfTerminal ((H ⋙ H').obj X) := by
  let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  let : GaloisCategory C'' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F'')
  have : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  have : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  have : PreGaloisCategory.FiberFunctor F'' := IsGaloisCategory.fiberFunctor F''
  constructor
  · intro htriv X
    refine (finiteCoproductTerminal_iff_trivialAction F'' ((H ⋙ H').obj X)).mpr fun σ y => ?_
    let e1 (x : F.obj X) := ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom x
    let e2 (z : F'.obj (H.obj X)) :=
      ConcreteCategory.hom (d'.actionIso.hom.app (H.obj X)).hom.hom z
    have hsurj1 : Function.Surjective e1 := ((bijective_hom_actionIso d X)).2
    have hsurj2 : Function.Surjective e2 := ((bijective_hom_actionIso d' (H.obj X))).2
    obtain ⟨z, rfl⟩ := hsurj2 y
    obtain ⟨x, rfl⟩ := hsurj1 z
    have hγ : d.hom.toMonoidHom (d'.hom.toMonoidHom σ) = 1 := by
      simpa using congrArg (fun f : Aut F'' →* Aut F => f σ) htriv
    have hrel' : e2 (e1 x) =
        (ConcreteCategory.hom (σ.hom.app (H'.obj (H.obj X)))) (e2 (e1 x)) := by
      have hrel := hcomp F F' F'' H H' t t' d d' X σ x
      change e2 (e1 ((ConcreteCategory.hom
        ((d.hom.toMonoidHom (d'.hom.toMonoidHom σ)).hom.app X)) x)) = _ at hrel
      rw [hγ] at hrel
      change e2 (e1 x) = _ at hrel
      simpa [e1, e2] using hrel
    exact hrel'.symm
  · intro hall
    apply MonoidHom.ext
    intro σ
    apply Aut.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.ext
    apply TypeCat.Fun.ext
    funext x
    let e1 (x : F.obj X) := ConcreteCategory.hom (d.actionIso.hom.app X).hom.hom x
    let e2 (z : F'.obj (H.obj X)) :=
      ConcreteCategory.hom (d'.actionIso.hom.app (H.obj X)).hom.hom z
    have hinj1 : Function.Injective e1 := ((bijective_hom_actionIso d X)).1
    have hinj2 : Function.Injective e2 := ((bijective_hom_actionIso d' (H.obj X))).1
    have htriv :=
      (finiteCoproductTerminal_iff_trivialAction F'' ((H ⋙ H').obj X)).mp (hall X)
    have hrel := hcomp F F' F'' H H' t t' d d' X σ x
    show ConcreteCategory.hom
        (((d.hom.toMonoidHom.comp d'.hom.toMonoidHom) σ).hom.app X) x = x
    apply hinj1
    apply hinj2
    change e2 (e1 ((ConcreteCategory.hom
      ((d.hom.toMonoidHom (d'.hom.toMonoidHom σ)).hom.app X)) x)) = _ at hrel
    simpa [e1, e2] using hrel.trans (htriv σ (e2 (e1 x)))

end CategoryTheory
