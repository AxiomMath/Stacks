module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.TrivialComposite
public import Mathlib.CategoryTheory.Galois.EssSurj
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Tactic.Group
public import StacksCore.Tactic.StacksAttribute

/-!
# Normal images in the functoriality of Galois categories

For an exact functor between Galois categories, the image of the induced homomorphism of
automorphism groups is normal exactly when every connected object whose image receives a map
from a final object has image a finite coproduct of final objects.

## Main results

* `CategoryTheory.normal_range_iff_connected_image_finite_coproduct_of_terminal` gives the
  characterization of normality.

## Implementation notes

Only the second functor of the diagram is needed. The final object is expressed by the existence
of any terminal object mapping to the image; the coproduct condition uses
`CategoryTheory.IsFiniteCoproductOfTerminal`.

## References

* [Stacks Project, Tag 0BTS](https://stacks.math.columbia.edu/tag/0BTS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u' v' u'' v'' w
universe uG

namespace CategoryTheory

variable {C : Type u'} [Category.{v'} C]

private def actionIsoOfContActionIso {G : Type*} [Group G] [TopologicalSpace G]
    {A B : ContAction FintypeCat.{w} G} (e : A ≅ B) : A.obj ≅ B.obj := by
  refine ⟨e.hom.hom, e.inv.hom, ?_, ?_⟩
  · ext x
    exact congrArg (fun f => f.hom.hom x) (Iso.hom_inv_id e)
  · ext x
    exact congrArg (fun f => f.hom.hom x) (Iso.inv_hom_id e)

private theorem normal_range_iff_open_overgroups
    {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (f : G →ₜ* K) :
    (MonoidHom.range f.toMonoidHom).Normal ↔
      ∀ U : OpenSubgroup K, (∀ x : G, f x ∈ U) →
        ∀ g : K, ∀ x : G, g * f x * g⁻¹ ∈ U := by
  constructor
  · intro hN U hU g x
    have hc : g * f x * g⁻¹ ∈ MonoidHom.range f.toMonoidHom :=
      hN.conj_mem _ ⟨x, rfl⟩ g
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hc
    rw [← hy]
    exact hU y
  · intro hU
    let L : ClosedSubgroup K :=
      { toSubgroup := MonoidHom.range f.toMonoidHom
        isClosed' := by
          show IsClosed (Set.range f.toContinuousMap)
          simpa only [Set.image_univ] using (isCompact_univ.image f.continuous).isClosed }
    refine ⟨fun a ha g ↦ ?_⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
    show g * f x * g⁻¹ ∈ (L : Subgroup K)
    rw [ProfiniteGrp.closedSubgroup_eq_sInf_open L]
    exact Subgroup.mem_sInf.mpr fun N hN ↦ hU ⟨N, hN.1⟩ (fun y ↦ hN.2 ⟨y, rfl⟩) g x

/-- The fiber of a fiber functor at a terminal object has a unique element. -/
private theorem nonempty_unique_fiber_of_isTerminal
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    {Z : C} (hZ : IsTerminal Z) : Nonempty (Unique (F.obj Z)) :=
  ⟨Types.isTerminalEquivUnique _ (hZ.isTerminalObj (setValuedFiberFunctor F) Z)⟩

/-- Automorphisms of a fiber functor fix the image of a point of a terminal fiber. -/
private theorem smul_map_of_isTerminal
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    {Z Y : C} (hZ : IsTerminal Z) (f : Z ⟶ Y) (σ : Aut F) (z : F.obj Z) :
    σ • (F.map f) z = (F.map f) z := by
  obtain ⟨_⟩ := nonempty_unique_fiber_of_isTerminal F hZ
  have hz : σ • z = z := Subsingleton.elim _ _
  simpa only [hz] using (PreGaloisCategory.mulAction_naturality F σ f z)

private theorem fixed_point_of_terminal_map
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    {Z Y : C} (hZ : IsTerminal Z) (f : Z ⟶ Y) :
    ∃ y : F.obj Y, ∀ σ : Aut F, σ • y = y := by
  obtain ⟨_⟩ := nonempty_unique_fiber_of_isTerminal F hZ
  exact ⟨(F.map f) default, fun σ => smul_map_of_isTerminal F hZ f σ _⟩

private theorem fixed_point_gives_morphism
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    {S Y : C} [Unique (F.obj S)] (y : F.obj Y)
    (hy : ∀ g : Aut F, g • y = y) : Nonempty (S ⟶ Y) := by
  let p : (PreGaloisCategory.functorToAction F).obj S ⟶
      (PreGaloisCategory.functorToAction F).obj Y :=
    { hom := FintypeCat.homMk (fun _ => y)
      comm := by
        intro g
        ext z
        show y = g • y
        exact (hy g).symm }
  obtain ⟨f, -⟩ := (PreGaloisCategory.functorToAction F).map_surjective p
  exact ⟨f⟩

private theorem action_trivial_of_finite_coproduct_terminal
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    (Y : C) (hY : IsFiniteCoproductOfTerminal Y) :
    ∀ σ : Aut F, ∀ y : F.obj Y, σ • y = y := by
  classical
  obtain ⟨n, A, f, hterm, ⟨hc⟩⟩ := hY
  let G := setValuedFiberFunctor F
  have hcG : IsColimit (Cofan.mk (G.obj Y) (fun i => G.map (f i))) :=
    isColimitCofanMkObjOfIsColimit G A f hc
  intro σ y
  obtain ⟨i, a, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hcG y
  exact smul_map_of_isTerminal F (hterm i).some (f i) σ a

private theorem inducedHom_app_apply
    {C : Type u'} [Category.{v'} C] {D : Type u''} [Category.{v''} D]
    (F : C ⥤ FintypeCat.{w}) (F' : D ⥤ FintypeCat.{w}) (H : C ⥤ D)
    (t : H ⋙ F' ≅ F) (σ : Aut F') (X : C) (y : (F'.obj (H.obj X)).obj) :
    ((inducedHom F F' H t σ).hom.app X) ((t.hom.app X) y) =
      (t.hom.app X) ((σ.hom.app (H.obj X)) y) := by
  let β := ((Functor.whiskeringLeft C D FintypeCat).obj H).mapAut F' σ
  have hβ : β.hom.app X = σ.hom.app (H.obj X) := rfl
  show ((t.conjAut β).hom.app X) ((t.hom.app X) y) = _
  rw [Iso.conjAut_apply]
  show ((t.symm.hom.app X ≫ β.hom.app X ≫ t.hom.app X).hom) ((t.hom.app X) y) = _
  simp [hβ]

private theorem finite_coproduct_terminal_of_action_trivial
    {C : Type u'} [Category.{v'} C] (F : C ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [GaloisCategory C] [PreGaloisCategory.FiberFunctor F]
    (Y : C) (htriv : ∀ σ : Aut F, ∀ y : F.obj Y, σ • y = y) :
    IsFiniteCoproductOfTerminal Y := by
  classical
  let G := setValuedFiberFunctor F
  obtain ⟨ι, A, f, hc, hfin, hconn⟩ :=
    IsGaloisCategory.exists_finite_coproduct_connected (F := G) Y
  let : Finite ι := hfin
  have hcG : IsColimit (Cofan.mk (G.obj Y) (fun i => G.map (f i))) :=
    isColimitCofanMkObjOfIsColimit G A f hc
  have : F.ReflectsIsomorphisms := reflectsIsomorphisms_of_comp F FintypeCat.incl
  let star : C := ⊤_ C
  have hstar : IsTerminal star := terminalIsTerminal
  obtain ⟨_⟩ := nonempty_unique_fiber_of_isTerminal F hstar
  have hterm (i : ι) : Nonempty (IsTerminal (A i)) := by
    have : PreGaloisCategory.IsConnected (A i) := hconn i
    have : Nonempty ((F.obj (A i)).obj) :=
      PreGaloisCategory.nonempty_fiber_of_isConnected F (A i)
    have hsub : Subsingleton ((F.obj (A i)).obj) := by
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) a b
      let aF : (F.obj (A i)).obj := a
      exact Cofan.inj_injective_of_isColimit hcG i <| calc
        (G.map (f i)) a = g • ((F.map (f i)) aF) := (htriv g _).symm
        _ = (G.map (f i)) (g • aF) := PreGaloisCategory.mulAction_naturality F g (f i) aF
        _ = (G.map (f i)) b := by rw [hg]
    have : Unique ((F.obj (A i)).obj) :=
      uniqueOfSubsingleton (Classical.arbitrary ((F.obj (A i)).obj))
    let a : (F.obj (A i)).obj := default
    obtain ⟨q⟩ := fixed_point_gives_morphism F (S := star) (Y := A i) a
      fun _ => Subsingleton.elim _ _
    have : IsIso (F.map q) := (ConcreteCategory.isIso_iff_bijective (F.map q)).mpr
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have : IsIso q := isIso_of_reflects_iso q F
    exact ⟨hstar.ofIso (asIso q)⟩
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hcFin : IsColimit (Cofan.mk Y (fun j : Fin (Fintype.card ι) => f (e j))) :=
    (Cofan.isColimitEquivOfEquiv e (Cofan.mk Y f)) hc
  exact ⟨Fintype.card ι, A ∘ e, (fun j => f (e j)), (fun j => hterm (e j)), ⟨hcFin⟩⟩

/-- Normality of the image of the homomorphism induced by an exact functor of Galois categories
is equivalent to the terminal-object criterion on images of connected objects. -/
@[stacks 0BTS]
public theorem normal_range_iff_connected_image_finite_coproduct_of_terminal
    {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
    (F' : C' ⥤ FintypeCat.{w}) (F'' : C'' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F')]
    [IsGaloisCategory (setValuedFiberFunctor F'')]
    (H' : C' ⥤ C'')
    (t' : H' ⋙ F'' ≅ F') (d' : GaloisFunctorData F' F'' H' t') :
    (MonoidHom.range d'.hom.toMonoidHom).Normal ↔
      ∀ X' : C', PreGaloisCategory.IsConnected X' →
        (∃ Z : C'', Nonempty (IsTerminal Z) ∧ Nonempty (Z ⟶ H'.obj X')) →
          IsFiniteCoproductOfTerminal (H'.obj X') := by
  classical
  let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  let : PreGaloisCategory C'' := preGalois_of_isGaloisCategory F''
  let : PreGaloisCategory.FiberFunctor F'' := IsGaloisCategory.fiberFunctor F''
  let : GaloisCategory C'' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F'')
  constructor
  · rintro hnormal X' hconn ⟨Z, ⟨hZ⟩, ⟨f⟩⟩
    obtain ⟨y, hy⟩ := fixed_point_of_terminal_map F'' hZ f
    let x : (F'.obj X').obj := (t'.hom.app X').hom y
    have hmapAuto (σ : Aut F'') :
        d'.hom σ = inducedHom F' F'' H' t' σ := by
      show d'.hom.toMonoidHom σ = _
      exact congrArg (fun m : Aut F'' →* Aut F' => m σ) d'.hom_toMonoidHom
    have hx : ∀ σ : Aut F'', d'.hom σ • x = x := by
      intro σ
      have hfix := inducedHom_app_apply F' F'' H' t' σ X' y
      rw [← hmapAuto σ] at hfix
      show d'.hom σ • x = x
      have hy' : (σ.hom.app (H'.obj X')) y = y := by
        simpa only [PreGaloisCategory.mulAction_def] using hy σ
      simpa [x, PreGaloisCategory.mulAction_def, hy'] using hfix
    have : Nonempty ((F'.obj X').obj) :=
      PreGaloisCategory.nonempty_fiber_of_isConnected F' X'
    have htriv : ∀ σ : Aut F'', ∀ a : (F'.obj X').obj, d'.hom σ • a = a := by
      intro σ a
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut F') x a
      have hconj : g⁻¹ * d'.hom σ * g ∈ MonoidHom.range d'.hom.toMonoidHom :=
        hnormal.conj_mem _ ⟨σ, rfl⟩ g⁻¹
      obtain ⟨τ, hτ⟩ := MonoidHom.mem_range.mp hconj
      calc
        d'.hom σ • g • x = g • (g⁻¹ * d'.hom σ * g) • x := by simp [mul_smul]
        _ = g • x := by rw [← hτ]; exact congrArg (g • ·) (hx τ)
    refine finite_coproduct_terminal_of_action_trivial F'' (H'.obj X') fun σ a ↦ ?_
    let b : (F'.obj X').obj := (t'.hom.app X') a
    have hcomm := htriv σ b
    change ((d'.hom σ).hom.app X') b = b at hcomm
    rw [hmapAuto σ, inducedHom_app_apply F' F'' H' t' σ X' a] at hcomm
    have hinj : Function.Injective (t'.hom.app X') :=
      ((ConcreteCategory.isIso_iff_bijective (t'.hom.app X')).mp inferInstance).1
    have h' : (σ.hom.app (H'.obj X')) a = a := hinj (by simpa [b] using hcomm)
    simpa only [b, PreGaloisCategory.mulAction_def] using h'
  · intro hobjects
    refine (normal_range_iff_open_overgroups d'.hom).2 fun U hU g σ ↦ ?_
    let Q := quotientContActionSwitch U
    have hess : (PreGaloisCategory.functorToContAction F').EssSurj := inferInstance
    obtain ⟨X', ⟨e⟩⟩ := hess.mem_essImage Q
    have : MulAction.IsPretransitive (Aut F') (quotientContAction U).obj.V := by
      show MulAction.IsPretransitive (Aut F') (Aut F' ⧸ U.toSubgroup)
      infer_instance
    have : MulAction.IsPretransitive (Aut F') Q.obj.V :=
      pretransitive_uSwitch (A := (quotientContAction U).obj)
    let eA := actionIsoOfContActionIso e
    let qid : Q.obj.V :=
      (FintypeCat.uSwitchEquiv (quotientContAction U).obj.V).symm
        (⟦1⟧ : Aut F' ⧸ U.toSubgroup)
    have : Nonempty ((F'.obj X').obj) := ⟨eA.inv.hom.hom qid⟩
    have : MulAction.IsPretransitive (Aut F') ((F'.obj X').obj) := by
      show MulAction.IsPretransitive (Aut F')
        (((PreGaloisCategory.functorToContAction F').obj X').obj.V)
      exact pretransitive_of_actionIso eA.symm
    let eH := (ContAction.res FintypeCat d'.hom).mapIso e.symm ≪≫ d'.actionIso.app X'
    let eHA := actionIsoOfContActionIso eH
    let y : (F''.obj (H'.obj X')).obj := eHA.hom.hom qid
    have hy : ∀ τ : Aut F'', τ • y = y := by
      intro τ
      have hcomm := ConcreteCategory.congr_hom (eHA.hom.comm τ) qid
      change eHA.hom.hom ((d'.hom τ) • qid) = τ • y at hcomm
      rw [fixed_quotientSwitch U (d'.hom τ) (hU τ)] at hcomm
      exact hcomm.symm
    obtain ⟨_⟩ := nonempty_unique_fiber_of_isTerminal F'' (terminalIsTerminal : IsTerminal (⊤_ C''))
    have htriv := action_trivial_of_finite_coproduct_terminal F'' (H'.obj X')
      (hobjects X' (isConnected_of_fiber_pretransitive F' X') ⟨⊤_ C'', ⟨terminalIsTerminal⟩,
        fixed_point_gives_morphism F'' (S := ⊤_ C'') (Y := H'.obj X') y hy⟩)
    let qg : Q.obj.V :=
      (FintypeCat.uSwitchEquiv (quotientContAction U).obj.V).symm
        (⟦g⁻¹⟧ : Aut F' ⧸ U.toSubgroup)
    let yg : (F''.obj (H'.obj X')).obj := eHA.hom.hom qg
    have hfix : d'.hom σ • qg = qg := by
      have hcomm := ConcreteCategory.congr_hom (eHA.hom.comm σ) qg
      change eHA.hom.hom ((d'.hom σ) • qg) = σ • yg at hcomm
      rw [htriv σ yg] at hcomm
      exact ((ConcreteCategory.isIso_iff_bijective eHA.hom.hom).mp inferInstance).1 hcomm
    let : MulAction (Aut F') (Aut F' ⧸ U.toSubgroup) :=
      MulAction.quotient (Aut F') U.toSubgroup
    have hq0 :
        (QuotientGroup.mk (d'.hom σ * g⁻¹) :
          (Action.FintypeCat.ofMulAction (Aut F')
            (FintypeCat.of (Aut F' ⧸ U.toSubgroup))).V.obj) =
        (QuotientGroup.mk g⁻¹ :
          (Action.FintypeCat.ofMulAction (Aut F')
            (FintypeCat.of (Aut F' ⧸ U.toSubgroup))).V.obj) := by
      change (FintypeCat.uSwitch.map
        ((quotientContAction U).obj.ρ (d'.hom σ))) _ = _ at hfix
      have h' := congrArg (FintypeCat.uSwitchEquiv (quotientContAction U).obj.V) hfix
      rw [← FintypeCat.uSwitchEquiv_naturality] at h'
      have hqg : FintypeCat.uSwitchEquiv (quotientContAction U).obj.V qg =
          (⟦g⁻¹⟧ : Aut F' ⧸ U.toSubgroup) := Equiv.apply_symm_apply _ _
      rw [hqg] at h'
      change ConcreteCategory.hom ((Aut F' ⧸ₐ U.toSubgroup).ρ (d'.hom σ))
        (QuotientGroup.mk g⁻¹) = _ at h'
      change (QuotientGroup.mk (d'.hom σ * g⁻¹) : Aut F' ⧸ U.toSubgroup) =
        QuotientGroup.mk g⁻¹ at h'
      exact h'
    simpa [mul_assoc] using U.inv_mem (QuotientGroup.eq.mp hq0)

end CategoryTheory
